//! Runtime-erased, finite predicate representations and located effects.
//! These are untrusted tables; unit validation checks their types and sources.
use crate::{VirLocation, VirMemoryAccess, VirOriginId, VirPredicateId, VirValueId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateRepresentation<T> {
    pub logic: crate::predicate_logic::PredicateLogic<T>,
    pub resources: Vec<PredicateStorage<T>>,
    pub bounds: Vec<PredicateWordBound>,
    pub prefixes: Vec<PredicateInitializedPrefix<T>>,
    pub witnesses: Vec<PredicateWitness<T>>,
}

impl<T: Copy + Eq> PredicateRepresentation<T> {
    pub(crate) fn has_valid_projected_witnesses(&self) -> bool {
        use crate::predicate_logic::{LogicNodeKind, ObservationTime};
        self.witnesses.iter().all(|field| {
            self.logic.existentials.iter().any(|binder| {
                field.name == binder.name && binder.default.as_ref().is_some_and(|expr| {
                    expr.root == 0 && expr.nodes.len() == 1 && expr.nodes[0].ty == binder.ty
                        && matches!(expr.nodes[0].kind, LogicNodeKind::Observe { resource, offset, access, time: ObservationTime::Current }
                            if resource == field.resource && offset == field.offset && access == field.ty)
                })
            })
        })
    }
    /// Existentials import fresh hidden values. Canonical field
    /// projections additionally retain the representation's field equation.
    /// Hidden resource positions carry identity only, never authority.
    pub(crate) fn has_supported_interface_witnesses(&self) -> bool {
        self.has_valid_projected_witnesses()
    }
}

/// A predicate-local existential whose explicit witness is a typed stored
/// scalar. The index is scoped by its enclosing declaration, never globally
/// interchangeable with another predicate or runtime instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateWitness<T> {
    pub name: String,
    pub ty: T,
    pub resource: u32,
    pub offset: u64,
}

/// A prefix count is either a canonical stored cursor or an instantiated
/// logical expression. Neither form establishes any initialized bytes by itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PredicatePrefixCount<T> {
    Stored { offset: u64 },
    Logical(crate::predicate_logic::LogicExpression<T>),
}

/// A same-allocation array prefix selected by a typed count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateInitializedPrefix<T> {
    pub resource: u32,
    pub array_offset: u64,
    pub element: T,
    pub length: u64,
    pub stride: u64,
    pub count: PredicatePrefixCount<T>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateStorage<T> {
    pub name: String,
    pub pointee: T,
    /// Allocation-relative half-open byte intervals, independent of SSA IDs.
    pub initialized: Vec<(u64, u64)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PredicateWordBound {
    pub resource: u32,
    pub offset: u64,
    pub lower: u64,
    pub upper: u64,
}

pub type VirPredicateRepresentation = PredicateRepresentation<VirMemoryAccess>;

/// Canonical finite field plan. This describes storage, never authority: the
/// resource adapter must find a matching live payload at every selected cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PredicateResourceField {
    pub offset: u64,
    pub access: VirMemoryAccess,
    pub pointee: VirMemoryAccess,
    pub kind: crate::VirPointerKind,
    pub mutability: crate::VirMutability,
    pub size: u64,
    pub value_bytes: Vec<(u64, u64)>,
}

pub(crate) fn predicate_resource_fields(
    memory: &crate::VirMemorySchema,
    root: VirMemoryAccess,
) -> Option<Vec<PredicateResourceField>> {
    // Reject unsupported leaves independently of source/HIR admission.
    // Inline layout is bounded separately from the single capability edge.
    let mut work = vec![(root.ty, 0usize, false)];
    let mut steps = 0usize;
    while let Some((ty, depth, behind_pointer)) = work.pop() {
        steps += 1;
        if depth > 16 || steps > 4096 {
            return None;
        }
        use crate::VirMemoryTypeKind as K;
        match memory.kind(ty)? {
            K::Unit | K::Bool | K::Integer(_) => {}
            K::Pointer {
                kind: crate::VirPointerKind::Raw,
                ..
            } => {}
            K::Pointer {
                pointee,
                kind: crate::VirPointerKind::Own | crate::VirPointerKind::Reference,
                ..
            } if !behind_pointer => work.push((*pointee, 0, true)),
            K::Array { element, length } if *length <= 4096 => {
                work.extend((0..*length).map(|_| (*element, depth + 1, behind_pointer)));
            }
            K::Tuple(elements) => {
                work.extend(elements.iter().map(|ty| (*ty, depth + 1, behind_pointer)))
            }
            K::Struct { fields } => {
                for field in fields {
                    work.push((memory.field(*field)?.ty, depth + 1, behind_pointer));
                }
            }
            _ => return None,
        }
        if work.len() > 4096 {
            return None;
        }
    }
    let shape = memory.object_shape(root).ok()?;
    if !shape.variants().is_empty() || shape.resource_leaves().len() > 256 {
        return None;
    }
    let mut fields = Vec::new();
    for leaf in shape.resource_leaves() {
        if leaf.kind() == crate::VirPointerKind::Raw {
            continue;
        }
        let child = memory.object_shape(leaf.pointee_access()).ok()?;
        // The first finite field profile has inline struct/tuple/array paths,
        // with one capability edge. Recursive pointer graphs remain gated.
        if !child.variants().is_empty()
            || child.size_bytes() == 0
            || child
                .resource_leaves()
                .iter()
                .any(|l| l.kind() != crate::VirPointerKind::Raw)
        {
            return None;
        }
        fields.push(PredicateResourceField {
            offset: leaf.bytes().start_bytes(),
            access: leaf.access(),
            pointee: leaf.pointee_access(),
            kind: leaf.kind(),
            mutability: leaf.mutability(),
            size: child.size_bytes(),
            value_bytes: child
                .value_bytes()
                .iter()
                .map(|b| (b.start_bytes(), b.end_bytes()))
                .collect(),
        });
    }
    Some(fields)
}

pub(crate) fn predicate_resource_access(
    memory: &crate::VirMemorySchema,
    body: &VirPredicateRepresentation,
    resource: u32,
    path: &[u64],
) -> Option<VirMemoryAccess> {
    let root = body.resources.get(resource as usize)?.pointee;
    match path {
        [] => Some(root),
        [offset] => predicate_resource_fields(memory, root)?
            .iter()
            .find(|field| field.offset == *offset)
            .map(|field| field.pointee),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VirPredicateBinding {
    pub pointer: VirValueId,
    pub permission: VirValueId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirPredicateActionKind {
    Fold {
        holder: u32,
        bindings: Vec<VirPredicateBinding>,
    },
    /// Reactivate existing runtime SSA carriers; no runtime value is created.
    Unfold {
        holder: u32,
        bindings: Vec<VirPredicateBinding>,
    },
    Move {
        source: u32,
        destination: u32,
    },
    Finish {
        holder: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirPredicateAction {
    pub id: u32,
    pub predicate: VirPredicateId,
    /// BlockEntry means before its first instruction; Instruction means after
    /// that instruction. Actions at the same point execute in table order.
    pub location: VirLocation,
    pub origin: VirOriginId,
    pub kind: VirPredicateActionKind,
    pub witnesses: crate::predicate_logic::WitnessArguments<VirMemoryAccess, VirValueId>,
}

/// A linear predicate at an ordinary function boundary. Slots name the
/// existing owner ABI, never an extra runtime argument or a trusted axiom.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateInterface<P, F, O> {
    pub predicate: P,
    pub function: F,
    pub ensures: bool,
    /// For an in-place postcondition, each pair names an input pointer slot
    /// and the restored parameter permission's output slot.
    pub in_place: bool,
    pub holder: u32,
    /// Direct owners use two slots in the same direction. Projected ensures
    /// use the aggregate result's hidden input pointer and output permission.
    pub bindings: Vec<(u32, u32)>,
    pub fields: Vec<Vec<crate::VirFieldId>>,
    /// Entry scalar slots and explicitly tagged result scalar slots; these
    /// are ghost expressions, not runtime effects.
    pub arguments: crate::predicate_logic::WitnessArguments<VirMemoryAccess, u32>,
    pub origin: O,
}
pub type VirPredicateInterface =
    PredicateInterface<VirPredicateId, crate::VirFunctionId, VirOriginId>;

/// Reconstruct scalar access from canonical layout, never from an untyped byte offset.
pub(crate) fn predicate_word_access(
    memory: &crate::VirMemorySchema,
    pointee: VirMemoryAccess,
    offset: u64,
) -> Option<VirMemoryAccess> {
    let shape = memory.object_shape(pointee).ok()?;
    shape
        .leaves()
        .iter()
        .find(|leaf| {
            leaf.bytes().start_bytes() == offset
                && leaf.bytes().len_bytes() == 8
                && matches!(
                    memory.kind(leaf.access().ty),
                    Some(crate::VirMemoryTypeKind::Integer(
                        crate::VirIntegerType::U64 | crate::VirIntegerType::Usize
                    ))
                )
        })
        .map(|leaf| leaf.access())
}

/// The witness cell is outside the selected backing and has a finite capacity bound.
pub(crate) fn prefix_bounds_valid<T>(
    p: &PredicateInitializedPrefix<T>,
    bounds: &[PredicateWordBound],
) -> bool {
    let Some(end) = p
        .stride
        .checked_mul(p.length)
        .and_then(|n| p.array_offset.checked_add(n))
    else {
        return false;
    };
    if p.length == 0 || p.stride == 0 {
        return false;
    }
    match &p.count {
        PredicatePrefixCount::Stored { offset } => offset.checked_add(8).is_some_and(|count_end| {
            (count_end <= p.array_offset || *offset >= end)
                && bounds
                    .iter()
                    .any(|b| b.resource == p.resource && b.offset == *offset && b.upper <= p.length)
        }),
        PredicatePrefixCount::Logical(_) => true,
    }
}

/// Resolve a bounded struct-only owner projection from canonical layouts.
pub(crate) fn predicate_owner_field(
    memory: &crate::VirMemorySchema,
    mut access: crate::VirMemoryAccess,
    path: &[crate::VirFieldId],
) -> Option<(u64, crate::VirMemoryAccess, crate::VirMemoryAccess)> {
    if path.is_empty() || path.len() > 16 {
        return None;
    }
    let mut offset = 0u64;
    for id in path {
        let crate::VirMemoryTypeKind::Struct { fields } = memory.kind(access.ty)? else {
            return None;
        };
        if !fields.contains(id) {
            return None;
        }
        let field = memory.field(*id)?;
        if field.owner != access.ty {
            return None;
        }
        offset = offset.checked_add(
            memory
                .layout(access.layout)?
                .fields
                .iter()
                .find(|f| f.field == *id)?
                .offset_bytes,
        )?;
        access = memory.access(field.ty)?;
    }
    let crate::VirMemoryTypeKind::Pointer {
        pointee,
        kind: crate::VirPointerKind::Own,
        ..
    } = memory.kind(access.ty)?
    else {
        return None;
    };
    Some((offset, access, memory.access(*pointee)?))
}

/// Independent logic/layout validation shared by unit admission and transfer.
pub(crate) fn validate_predicate_logic(
    memory: &crate::VirMemorySchema,
    body: &VirPredicateRepresentation,
) -> Result<(), crate::predicate_logic::LogicError> {
    if !body.has_valid_projected_witnesses() {
        return Err(crate::predicate_logic::LogicError::InvalidNode);
    }
    body.logic.validate(
        &body
            .resources
            .iter()
            .map(|r| r.name.as_str())
            .collect::<Vec<_>>(),
        &|resource, offset, access, time| {
            predicate_logic_observation(memory, body, resource, offset, access, time)
        },
        &|resource, path| predicate_resource_access(memory, body, resource, path),
    )
}

pub(crate) fn predicate_logic_observation(
    memory: &crate::VirMemorySchema,
    body: &VirPredicateRepresentation,
    resource: u32,
    offset: u64,
    access: VirMemoryAccess,
    time: crate::predicate_logic::ObservationTime,
) -> Option<crate::predicate_logic::LogicType<VirMemoryAccess>> {
    use crate::predicate_logic::*;

    if time != ObservationTime::Current {
        return None;
    }
    let r = body.resources.get(resource as usize)?;
    if !memory
        .object_shape(r.pointee)
        .ok()?
        .leaves()
        .iter()
        .any(|l| l.bytes().start_bytes() == offset && l.access() == access)
    {
        return None;
    }
    match memory.kind(access.ty)? {
        crate::VirMemoryTypeKind::Bool => Some(LogicType::Bool),
        crate::VirMemoryTypeKind::Integer(crate::VirIntegerType::U64) => Some(LogicType::U64),
        crate::VirMemoryTypeKind::Integer(crate::VirIntegerType::Usize) => Some(LogicType::Usize),
        _ => None,
    }
}

pub(crate) fn validate_predicate_witnesses(
    memory: &crate::VirMemorySchema,
    body: &VirPredicateRepresentation,
    args: &crate::predicate_logic::WitnessArguments<VirMemoryAccess, VirValueId>,
) -> Result<(), crate::predicate_logic::LogicError> {
    use crate::predicate_logic::*;
    if !body.has_valid_projected_witnesses() {
        return Err(LogicError::InvalidNode);
    }
    args.validate(
        &body.logic,
        &|r, o, a, t| predicate_logic_observation(memory, body, r, o, a, t),
        &|r, path| predicate_resource_access(memory, body, r, path),
        &mut LogicBudget::default(),
    )
}
