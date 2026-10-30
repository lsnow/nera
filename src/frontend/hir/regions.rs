//! Canonical borrow-region identities and inclusion constraints.

use super::{HirFunctionId, HirRegionConstraintId, HirRegionId, HirScopeId, HirTypeId};
use crate::ByteSpan;

/// Source/producer role that introduced one borrow region.
///
/// Parameter and result regions are signature-visible. Lexical and inferred
/// regions are visible only in their owning scope and descendants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirRegionOrigin {
    LexicalScope {
        scope: HirScopeId,
    },
    Parameter {
        index: u32,
    },
    /// A function-owned binder for one reference leaf of a by-value aggregate
    /// parameter. `slot` is canonical inline field/element order, not an SSA ID.
    ParameterField {
        index: u32,
        slot: u32,
    },
    Result,
    Inferred {
        scope: HirScopeId,
    },
    /// A region-erased slot in a nominal aggregate declaration.
    ///
    /// Values stored in this slot retain their concrete loan identity in VIR;
    /// this HIR region is only the type-level binder for `&T` field syntax.
    AggregateErased,
}

impl HirRegionOrigin {
    /// Returns the lexical scope that bounds this region, when it has one.
    #[must_use]
    pub const fn lexical_scope(self) -> Option<HirScopeId> {
        match self {
            Self::LexicalScope { scope } | Self::Inferred { scope } => Some(scope),
            Self::Parameter { .. }
            | Self::ParameterField { .. }
            | Self::Result
            | Self::AggregateErased => None,
        }
    }
}

/// Enumerate reference leaves without following pointers or conflating two
/// occurrences of the same nominal erased region. This is bounded independently
/// of producer layout data and is shared by elaboration and HIR validation.
pub(super) fn aggregate_reference_slots(
    types: &[super::HirTypeDefinition],
    fields: &[super::HirField],
    root: HirTypeId,
) -> Option<Vec<HirRegionId>> {
    Some(
        aggregate_reference_types(types, fields, root)?
            .into_iter()
            .map(|(_, region)| region)
            .collect(),
    )
}

pub(super) fn aggregate_reference_types(
    types: &[super::HirTypeDefinition],
    fields: &[super::HirField],
    root: HirTypeId,
) -> Option<Vec<(HirTypeId, HirRegionId)>> {
    use super::HirTypeKind;
    let mut pending = vec![(root, 0usize)];
    let mut result = Vec::new();
    let mut steps = 0usize;
    while let Some((ty, depth)) = pending.pop() {
        steps += 1;
        if depth > 16 || steps > 4096 {
            return None;
        }
        match &types.get(ty.index())?.kind {
            HirTypeKind::Reference { region, .. } => {
                if result.len() == 256 {
                    return None;
                }
                result.push((ty, *region));
            }
            HirTypeKind::Struct { fields: members } => {
                if members.len() > 4096 - pending.len() {
                    return None;
                }
                // Match canonical VIR object paths, including independently
                // constructed HIR whose field-ID vector is not sorted.
                let mut members = members.clone();
                members.sort_unstable();
                for id in members.iter().rev() {
                    let field = fields.get(id.index())?;
                    if field.owner != ty {
                        return None;
                    }
                    pending.push((field.ty, depth + 1));
                }
            }
            HirTypeKind::Tuple(elements) => {
                if elements.len() > 4096 - pending.len() {
                    return None;
                }
                pending.extend(elements.iter().rev().map(|ty| (*ty, depth + 1)))
            }
            HirTypeKind::Array { element, length } => {
                if *length > 256 || *length as usize > 4096 - pending.len() {
                    return None;
                }
                pending.extend((0..*length).map(|_| (*element, depth + 1)));
            }
            HirTypeKind::Unit
            | HirTypeKind::Bool
            | HirTypeKind::Integer(_)
            | HirTypeKind::Own { .. }
            | HirTypeKind::RawPointer { .. } => {}
            _ => return None,
        }
        if pending.len() > 4096 {
            return None;
        }
    }
    Some(result)
}

/// Field binders inside the storage designated by a parameter. A direct
/// reference keeps its own Parameter binder; these are separate stored leaves.
pub(super) fn parameter_reference_types(
    types: &[super::HirTypeDefinition],
    fields: &[super::HirField],
    ty: HirTypeId,
) -> Option<Vec<(HirTypeId, HirRegionId)>> {
    let root = match types.get(ty.index())?.kind {
        super::HirTypeKind::Own { pointee } | super::HirTypeKind::Reference { pointee, .. } => {
            pointee
        }
        _ => ty,
    };
    if !matches!(
        types.get(root.index())?.kind,
        super::HirTypeKind::Struct { .. }
            | super::HirTypeKind::Array { .. }
            | super::HirTypeKind::Tuple(_)
    ) {
        return Some(Vec::new());
    }
    aggregate_reference_types(types, fields, root)
}

/// Entity that owns one canonical HIR borrow-region declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirRegionOwner {
    Function(HirFunctionId),
    Type(HirTypeId),
}

/// One canonical borrow region owned by a function or aggregate type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HirRegion {
    pub id: HirRegionId,
    pub owner: HirRegionOwner,
    pub origin: HirRegionOrigin,
    pub span: ByteSpan,
}

/// Canonical `subregion <= superregion` inclusion constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HirRegionConstraint {
    pub id: HirRegionConstraintId,
    pub owner: HirFunctionId,
    pub subregion: HirRegionId,
    pub superregion: HirRegionId,
    pub span: ByteSpan,
}

/// Canonical inline leaf range of a typed place. This never dereferences an
/// owner, raw pointer or reference, and never folds equal nominal regions.
pub(super) fn reference_leaf_range(
    types: &[super::HirTypeDefinition],
    fields: &[super::HirField],
    root: HirTypeId,
    projections: &[super::HirProjection],
) -> Option<(usize, usize)> {
    use super::{HirProjectionKind as P, HirTypeKind as T};
    let count = |ty| aggregate_reference_types(types, fields, ty).map(|v| v.len());
    let mut current = root;
    let mut projections = projections;
    if let Some(super::HirProjection {
        kind: P::Dereference,
        result_type,
        ..
    }) = projections.first()
    {
        match types.get(root.index())?.kind {
            T::Own { pointee } | T::Reference { pointee, .. } if pointee == *result_type => {
                current = pointee;
                projections = &projections[1..];
            }
            _ => return None,
        }
    }
    count(current)?;
    let mut start = 0usize;
    if projections.len() > 16 {
        return None;
    }
    for projection in projections {
        current = match (&types.get(current.index())?.kind, &projection.kind) {
            (T::Struct { fields: members }, P::Field { field }) => {
                let mut members = members.clone();
                members.sort_unstable();
                let index = members.iter().position(|id| id == field)?;
                for before in &members[..index] {
                    start = start.checked_add(count(fields.get(before.index())?.ty)?)?;
                }
                fields.get(field.index())?.ty
            }
            (T::Tuple(elements), P::TupleElement { index }) => {
                let index = usize::try_from(*index).ok()?;
                for before in elements.get(..index)? {
                    start = start.checked_add(count(*before)?)?;
                }
                *elements.get(index)?
            }
            (T::Array { element, length }, P::ConstantIndex { index }) if index < length => {
                start = start
                    .checked_add(count(*element)?.checked_mul(usize::try_from(*index).ok()?)?)?;
                *element
            }
            _ => return None,
        };
        if projection.result_type != current {
            return None;
        }
    }
    Some((start, count(current)?))
}

/// Region substitution for an aggregate value, in canonical reference-leaf
/// order. It carries no permission; VIR still proves actual resource identity.
pub(super) fn expression_reference_regions(
    types: &[super::HirTypeDefinition],
    fields: &[super::HirField],
    expression: &super::HirExpression,
    local: &impl Fn(super::HirLocalId) -> Option<(HirTypeId, Vec<HirRegionId>)>,
    call: &impl Fn(&super::HirCall, usize) -> Option<Vec<HirRegionId>>,
    depth: usize,
) -> Option<Vec<HirRegionId>> {
    use super::{HirExpressionKind as E, HirPlaceBase, HirTypeKind};
    if depth > 16 {
        return None;
    }
    let recurse = |e| expression_reference_regions(types, fields, e, local, call, depth + 1);
    let expected = aggregate_reference_types(types, fields, expression.ty)?;
    if expected.is_empty() {
        return Some(Vec::new());
    }
    let result = match &expression.kind {
        E::Read { place, .. } => {
            let HirPlaceBase::Local(id) = place.base;
            if place.projections.is_empty()
                && let HirTypeKind::Reference { region, .. } =
                    types.get(expression.ty.index())?.kind
            {
                return Some(vec![region]);
            }
            let (ty, regions) = local(id)?;
            let (start, count) = reference_leaf_range(types, fields, ty, &place.projections)?;
            regions.get(start..start.checked_add(count)?)?.to_vec()
        }
        E::StructConstructor { fields: values } => {
            let mut values = values.iter().collect::<Vec<_>>();
            values.sort_by_key(|v| v.field);
            let mut result = Vec::new();
            for value in values {
                result.extend(recurse(&value.value)?);
            }
            result
        }
        E::TupleConstructor { elements } | E::ArrayConstructor { elements } => {
            let mut result = Vec::new();
            for value in elements {
                result.extend(recurse(value)?);
            }
            result
        }
        E::ArrayRepeatConstructor { value, length } => {
            if *length > 256 {
                return None;
            }
            let regions = recurse(value)?;
            if regions.len().checked_mul(*length as usize)? > 256 {
                return None;
            }
            regions.repeat(*length as usize)
        }
        E::Call(c)
            if !matches!(
                types.get(expression.ty.index())?.kind,
                HirTypeKind::Reference { .. }
            ) =>
        {
            call(c, depth + 1)?
        }
        // A reference-producing expression's own binder was independently
        // validated by its borrowing/call rule. Aggregate call results need a
        // separate output-leaf relation and are not guessed from erased types.
        _ if matches!(
            types.get(expression.ty.index())?.kind,
            HirTypeKind::Reference { .. }
        ) =>
        {
            expected.iter().map(|(_, r)| *r).collect()
        }
        _ => return None,
    };
    (result.len() == expected.len()).then_some(result)
}

/// Region leaves in the storage designated by an owning/borrowed argument.
/// This selects typed storage; it never follows raw pointers or creates a loan.
pub(super) fn designated_reference_regions(
    types: &[super::HirTypeDefinition],
    fields: &[super::HirField],
    expression: &super::HirExpression,
    local: &impl Fn(super::HirLocalId) -> Option<(HirTypeId, Vec<HirRegionId>)>,
    call: &impl Fn(&super::HirCall, usize) -> Option<Vec<HirRegionId>>,
    depth: usize,
) -> Option<Vec<HirRegionId>> {
    use super::{HirExpressionKind as E, HirPlaceBase, HirTypeKind as T};
    if depth > 16 {
        return None;
    }
    if !matches!(
        types.get(expression.ty.index())?.kind,
        T::Own { .. } | T::Reference { .. }
    ) {
        return expression_reference_regions(types, fields, expression, local, call, depth);
    }
    let result = match &expression.kind {
        E::Read { place, .. } if place.projections.is_empty() => {
            let HirPlaceBase::Local(id) = place.base;
            local(id)?.1
        }
        E::Borrow { place, .. } => {
            let HirPlaceBase::Local(id) = place.base;
            let (ty, regions) = local(id)?;
            let (start, count) = reference_leaf_range(types, fields, ty, &place.projections)?;
            regions.get(start..start.checked_add(count)?)?.to_vec()
        }
        _ => return None,
    };
    (result.len() == parameter_reference_types(types, fields, expression.ty)?.len())
        .then_some(result)
}

/// A meet binder is constrained by both possible stored-field sources. This
/// is type/lifetime bookkeeping only; it carries no resource authority.
pub(super) const MAX_STORED_FIELD_REGION_CONSTRAINTS: usize = 4096;

pub(super) fn intersection_region(
    regions: &[HirRegion],
    constraints: &[HirRegionConstraint],
    owner: HirFunctionId,
    scope: HirScopeId,
    first: HirRegionId,
    second: HirRegionId,
) -> Option<HirRegionId> {
    if first == second {
        return Some(first);
    }
    if regions.get(first.index())?.origin == HirRegionOrigin::AggregateErased {
        return Some(second);
    }
    let expected = std::collections::BTreeSet::from([first, second]);
    regions
        .iter()
        .find(|r| {
            r.owner == HirRegionOwner::Function(owner)
                && r.origin == HirRegionOrigin::Inferred { scope }
                && constraints
                    .iter()
                    .filter(|c| c.owner == owner && c.subregion == r.id)
                    .map(|c| c.superregion)
                    .collect::<std::collections::BTreeSet<_>>()
                    == expected
        })
        .map(|r| r.id)
}

/// Reconstruct lexical bounds from actual borrow operands and all inferred
/// source constraints. A meet binder cannot hide a shorter lived stack slot.
/// This is only a lifetime bound; allocation/loan validity stays in the verifier.
pub(super) fn source_storage_scopes(
    body: &super::HirBody,
    regions: &[HirRegion],
    constraints: &[HirRegionConstraint],
    owner: HirFunctionId,
    root: HirRegionId,
) -> Option<std::collections::BTreeSet<HirScopeId>> {
    use super::visit::HirVisitor;
    use std::collections::{BTreeMap, BTreeSet};
    struct Borrows<'a> {
        body: &'a super::HirBody,
        scopes: BTreeMap<HirRegionId, BTreeSet<HirScopeId>>,
    }
    impl<'a> HirVisitor<'a> for Borrows<'a> {
        fn visit_expression(&mut self, expression: &'a super::HirExpression) {
            if let super::HirExpressionKind::Borrow { place, region, .. } = &expression.kind {
                let super::HirPlaceBase::Local(local) = place.base;
                if let Some(local) = self.body.locals.get(local.index()) {
                    self.scopes.entry(*region).or_default().insert(local.scope);
                }
            }
            super::visit::walk_expression(self, expression);
        }
    }
    let mut borrows = Borrows {
        body,
        scopes: BTreeMap::new(),
    };
    borrows.visit_block(&body.root);
    let mut pending = vec![root];
    let mut visited = BTreeSet::new();
    let mut result = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        if visited.len() > MAX_STORED_FIELD_REGION_CONSTRAINTS {
            return None;
        }
        let region = regions.get(id.index())?;
        if region.owner != HirRegionOwner::Function(owner) {
            return None;
        }
        let sources = constraints
            .iter()
            .filter(|c| c.owner == owner && c.subregion == id)
            .map(|c| c.superregion)
            .collect::<Vec<_>>();
        if let Some(scopes) = borrows.scopes.get(&id) {
            result.extend(scopes);
        } else if sources.is_empty()
            && let Some(scope) = region.origin.lexical_scope()
        {
            result.insert(scope);
        }
        pending.extend(sources);
    }
    Some(result)
}

#[cfg(test)]
mod source_bound_tests {
    use super::*;

    #[test]
    fn source_scope_traversal_fails_closed_above_the_region_budget() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "region-budget.nera",
            "fn main()->u64{return 0;}",
        ));
        let program = output.hir().unwrap();
        let function = &program.functions()[0];
        let body = function.body().unwrap();
        for count in [
            MAX_STORED_FIELD_REGION_CONSTRAINTS,
            MAX_STORED_FIELD_REGION_CONSTRAINTS + 1,
        ] {
            let regions = (0..count)
                .map(|i| HirRegion {
                    id: HirRegionId::new(i as u32),
                    owner: HirRegionOwner::Function(function.id),
                    origin: HirRegionOrigin::Inferred {
                        scope: body.root.scope,
                    },
                    span: body.root.span,
                })
                .collect::<Vec<_>>();
            let constraints = (0..count - 1)
                .map(|i| HirRegionConstraint {
                    id: HirRegionConstraintId::new(i as u32),
                    owner: function.id,
                    subregion: regions[i].id,
                    superregion: regions[i + 1].id,
                    span: body.root.span,
                })
                .collect::<Vec<_>>();
            let scopes =
                source_storage_scopes(body, &regions, &constraints, function.id, regions[0].id);
            if count == MAX_STORED_FIELD_REGION_CONSTRAINTS {
                assert_eq!(
                    scopes,
                    Some(std::collections::BTreeSet::from([body.root.scope]))
                );
            } else {
                assert_eq!(scopes, None);
            }
        }
    }
}
