//! Pure, target-layout-driven resolution of typed HIR places.

use std::error::Error;
use std::fmt;

use super::{
    HirBody, HirExpression, HirFieldId, HirFunctionId, HirIntegerType, HirLayout, HirLocal,
    HirMutability, HirPlace, HirPlaceBase, HirProgram, HirProjectionKind, HirTypeId, HirTypeKind,
    HirVariantId,
};
use crate::ByteSpan;
use crate::diagnostic::span_contains;

/// Access requested by a consumer of a resolved place.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirPlaceAccess {
    Read,
    Write,
}

/// Where the runtime upper bound for an index or range comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirBoundsSource {
    Array { length: u64 },
    Slice { slice_type: HirTypeId },
}

/// One canonical, layout-aware projection step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedHirProjection<'place> {
    pub kind: ResolvedHirProjectionKind<'place>,
    pub input_type: HirTypeId,
    pub output_type: HirTypeId,
    /// Alignment required by an access to the resulting place.
    pub required_alignment: u64,
    /// Offset from the most recent dereference when it is statically known.
    pub static_offset_bytes: Option<u64>,
    pub span: ByteSpan,
}

/// Projection facts needed by later VIR lowering and verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedHirProjectionKind<'place> {
    Dereference {
        pointer_type: HirTypeId,
        pointee: HirTypeId,
    },
    Field {
        field: HirFieldId,
        offset_bytes: u64,
    },
    TupleElement {
        index: u64,
        offset_bytes: u64,
    },
    ConstantIndex {
        index: u64,
        bounds: HirBoundsSource,
        stride_bytes: u64,
        offset_bytes: u64,
    },
    DynamicIndex {
        index: &'place HirExpression,
        bounds: HirBoundsSource,
        stride_bytes: u64,
    },
    Slice {
        start: Option<&'place HirExpression>,
        end: Option<&'place HirExpression>,
        bounds: HirBoundsSource,
        stride_bytes: u64,
        mutability: HirMutability,
    },
    Downcast {
        variant: HirVariantId,
        payload_offset_bytes: u64,
    },
}

/// A place resolved against one function body and the program's target layout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedHirPlace<'place> {
    pub base: HirPlaceBase,
    pub base_type: HirTypeId,
    pub projections: Vec<ResolvedHirProjection<'place>>,
    pub ty: HirTypeId,
    pub writable: bool,
    pub required_alignment: u64,
    pub static_offset_bytes: Option<u64>,
    pub span: ByteSpan,
}

/// Stable class of a place-resolution failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HirPlaceResolutionErrorKind {
    MissingFunction,
    MissingBody,
    MissingLocal,
    MissingType,
    MissingLayout,
    InvalidLayout,
    InvalidDereference,
    InvalidField,
    InvalidIndex,
    InvalidSlice,
    InvalidDowncast,
    TypeMismatch,
    SpanMismatch,
    ImmutableWrite,
    ArithmeticOverflow,
}

/// A fail-closed resolver error tied to a place or projection span.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HirPlaceResolutionError {
    kind: HirPlaceResolutionErrorKind,
    projection_index: Option<usize>,
    span: ByteSpan,
}

impl HirPlaceResolutionError {
    #[must_use]
    pub const fn kind(self) -> HirPlaceResolutionErrorKind {
        self.kind
    }

    #[must_use]
    pub const fn projection_index(self) -> Option<usize> {
        self.projection_index
    }

    #[must_use]
    pub const fn span(self) -> ByteSpan {
        self.span
    }

    #[must_use]
    pub const fn problem(self) -> &'static str {
        match self.kind {
            HirPlaceResolutionErrorKind::MissingFunction => "place function is missing",
            HirPlaceResolutionErrorKind::MissingBody => "place function has no body",
            HirPlaceResolutionErrorKind::MissingLocal => "place has missing local base",
            HirPlaceResolutionErrorKind::MissingType => "place references a missing type",
            HirPlaceResolutionErrorKind::MissingLayout => "place type has no resolved layout",
            HirPlaceResolutionErrorKind::InvalidLayout => {
                "place uses an inconsistent target layout"
            }
            HirPlaceResolutionErrorKind::InvalidDereference => {
                "dereference projection requires a pointer-like type"
            }
            HirPlaceResolutionErrorKind::InvalidField => {
                "field projection does not belong to the current aggregate"
            }
            HirPlaceResolutionErrorKind::InvalidIndex => {
                "index projection requires a valid array or slice index"
            }
            HirPlaceResolutionErrorKind::InvalidSlice => {
                "slice projection has invalid bounds or result type"
            }
            HirPlaceResolutionErrorKind::InvalidDowncast => {
                "downcast variant does not belong to the current enum"
            }
            HirPlaceResolutionErrorKind::TypeMismatch => {
                "place or projection result type does not match the resolved type"
            }
            HirPlaceResolutionErrorKind::SpanMismatch => {
                "projection operand span is outside its parent span"
            }
            HirPlaceResolutionErrorKind::ImmutableWrite => {
                "place is not writable for the requested access"
            }
            HirPlaceResolutionErrorKind::ArithmeticOverflow => {
                "place layout arithmetic overflows u64"
            }
        }
    }
}

impl fmt::Display for HirPlaceResolutionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(index) = self.projection_index {
            write!(
                formatter,
                "cannot resolve HIR place projection {index}: {}",
                self.problem()
            )
        } else {
            write!(formatter, "cannot resolve HIR place: {}", self.problem())
        }
    }
}

impl Error for HirPlaceResolutionError {}

impl HirProgram {
    /// Resolves one place in a function body using only validated HIR tables
    /// and the program's explicit target layout.
    pub fn resolve_place<'place>(
        &self,
        function: HirFunctionId,
        place: &'place HirPlace,
        access: HirPlaceAccess,
    ) -> Result<ResolvedHirPlace<'place>, HirPlaceResolutionError> {
        let function = self.function_by_id(function).ok_or_else(|| {
            place_error(
                HirPlaceResolutionErrorKind::MissingFunction,
                None,
                place.span,
            )
        })?;
        let body = function.body().ok_or_else(|| {
            place_error(HirPlaceResolutionErrorKind::MissingBody, None, place.span)
        })?;
        resolve_place_with_locals(self, body, place, access)
    }
}

pub(super) fn resolve_place_with_locals<'place>(
    program: &HirProgram,
    body: &HirBody,
    place: &'place HirPlace,
    access: HirPlaceAccess,
) -> Result<ResolvedHirPlace<'place>, HirPlaceResolutionError> {
    resolve_place_from_locals(program, &body.locals, place, access)
}

pub(super) fn resolve_place_from_locals<'place>(
    program: &HirProgram,
    locals: &[HirLocal],
    place: &'place HirPlace,
    access: HirPlaceAccess,
) -> Result<ResolvedHirPlace<'place>, HirPlaceResolutionError> {
    let HirPlaceBase::Local(local_id) = place.base;
    let local = locals
        .get(local_id.index())
        .filter(|local| local.id == local_id)
        .ok_or_else(|| place_error(HirPlaceResolutionErrorKind::MissingLocal, None, place.span))?;
    let base_layout = require_layout(program, local.ty, None, place.span)?;
    if base_layout.id != local.layout {
        return Err(place_error(
            HirPlaceResolutionErrorKind::InvalidLayout,
            None,
            place.span,
        ));
    }

    let mut state = ResolutionState {
        ty: local.ty,
        writable: local.mutable,
        downcast: None,
        required_alignment: base_layout.alignment,
        static_offset_bytes: Some(0),
    };
    let base_type = local.ty;
    let mut projections = Vec::with_capacity(place.projections.len());

    for (index, projection) in place.projections.iter().enumerate() {
        if !span_contains(place.span, projection.span) {
            return Err(place_error(
                HirPlaceResolutionErrorKind::SpanMismatch,
                Some(index),
                projection.span,
            ));
        }
        if program.type_definition(projection.result_type).is_none() {
            return Err(place_error(
                HirPlaceResolutionErrorKind::MissingType,
                Some(index),
                projection.span,
            ));
        }
        let input_type = state.ty;
        let resolved_kind = match &projection.kind {
            HirProjectionKind::Dereference => {
                require_layout(program, state.ty, Some(index), projection.span)?;
                let (pointee, writable) = match program.type_kind(state.ty) {
                    Some(HirTypeKind::Own { pointee }) => (*pointee, true),
                    Some(HirTypeKind::RawPointer {
                        pointee,
                        mutability,
                    })
                    | Some(HirTypeKind::Reference {
                        pointee,
                        mutability,
                        ..
                    }) => (*pointee, *mutability == HirMutability::Mutable),
                    _ => {
                        return Err(place_error(
                            HirPlaceResolutionErrorKind::InvalidDereference,
                            Some(index),
                            projection.span,
                        ));
                    }
                };
                state.ty = pointee;
                state.writable = writable;
                state.downcast = None;
                state.required_alignment =
                    access_alignment(program, pointee, Some(index), projection.span)?;
                state.static_offset_bytes = Some(0);
                ResolvedHirProjectionKind::Dereference {
                    pointer_type: input_type,
                    pointee,
                }
            }
            HirProjectionKind::Field { field } => {
                let field_definition = program.field(*field).ok_or_else(|| {
                    place_error(
                        HirPlaceResolutionErrorKind::InvalidField,
                        Some(index),
                        projection.span,
                    )
                })?;
                let owner_layout = require_layout(program, state.ty, Some(index), projection.span)?;
                let offset_bytes = field_offset(
                    program,
                    owner_layout,
                    state.ty,
                    state.downcast,
                    *field,
                    index,
                    projection.span,
                )?;
                let field_layout =
                    require_layout(program, field_definition.ty, Some(index), projection.span)?;
                let absolute_offset = state
                    .static_offset_bytes
                    .and_then(|offset| offset.checked_add(offset_bytes));
                if state.static_offset_bytes.is_some() && absolute_offset.is_none() {
                    return Err(place_error(
                        HirPlaceResolutionErrorKind::ArithmeticOverflow,
                        Some(index),
                        projection.span,
                    ));
                }
                state.ty = field_definition.ty;
                state.downcast = None;
                state.required_alignment = field_layout.alignment;
                state.static_offset_bytes = absolute_offset;
                ResolvedHirProjectionKind::Field {
                    field: *field,
                    offset_bytes,
                }
            }
            HirProjectionKind::TupleElement {
                index: element_index,
            } => {
                let (element, offset_bytes) =
                    tuple_element(program, state.ty, *element_index, index, projection.span)?;
                let element_layout =
                    require_layout(program, element, Some(index), projection.span)?;
                state.ty = element;
                state.downcast = None;
                state.required_alignment = element_layout.alignment;
                state.static_offset_bytes = checked_static_add(
                    state.static_offset_bytes,
                    offset_bytes,
                    index,
                    projection.span,
                )?;
                ResolvedHirProjectionKind::TupleElement {
                    index: *element_index,
                    offset_bytes,
                }
            }
            HirProjectionKind::ConstantIndex {
                index: element_index,
            } => {
                let indexed = indexed_type(program, state, index, projection.span)?;
                if let HirBoundsSource::Array { length } = indexed.bounds
                    && *element_index >= length
                {
                    return Err(place_error(
                        HirPlaceResolutionErrorKind::InvalidIndex,
                        Some(index),
                        projection.span,
                    ));
                }
                let offset_bytes =
                    element_index
                        .checked_mul(indexed.stride_bytes)
                        .ok_or_else(|| {
                            place_error(
                                HirPlaceResolutionErrorKind::ArithmeticOverflow,
                                Some(index),
                                projection.span,
                            )
                        })?;
                state.ty = indexed.element;
                state.writable = indexed.writable;
                state.downcast = None;
                state.required_alignment = indexed.alignment;
                state.static_offset_bytes = checked_static_add(
                    state.static_offset_bytes,
                    offset_bytes,
                    index,
                    projection.span,
                )?;
                ResolvedHirProjectionKind::ConstantIndex {
                    index: *element_index,
                    bounds: indexed.bounds,
                    stride_bytes: indexed.stride_bytes,
                    offset_bytes,
                }
            }
            HirProjectionKind::DynamicIndex { index: operand } => {
                if !span_contains(projection.span, operand.span)
                    || program.type_kind(operand.ty)
                        != Some(&HirTypeKind::Integer(HirIntegerType::Usize))
                {
                    return Err(place_error(
                        HirPlaceResolutionErrorKind::InvalidIndex,
                        Some(index),
                        operand.span,
                    ));
                }
                let indexed = indexed_type(program, state, index, projection.span)?;
                state.ty = indexed.element;
                state.writable = indexed.writable;
                state.downcast = None;
                state.required_alignment = indexed.alignment;
                state.static_offset_bytes = None;
                ResolvedHirProjectionKind::DynamicIndex {
                    index: operand,
                    bounds: indexed.bounds,
                    stride_bytes: indexed.stride_bytes,
                }
            }
            HirProjectionKind::Slice { start, end } => {
                for bound in start.iter().chain(end) {
                    if !span_contains(projection.span, bound.span)
                        || program.type_kind(bound.ty)
                            != Some(&HirTypeKind::Integer(HirIntegerType::Usize))
                    {
                        return Err(place_error(
                            HirPlaceResolutionErrorKind::InvalidSlice,
                            Some(index),
                            bound.span,
                        ));
                    }
                }
                let indexed = indexed_type(program, state, index, projection.span)?;
                let Some(HirTypeKind::Slice {
                    element,
                    mutability,
                }) = program.type_kind(projection.result_type)
                else {
                    return Err(place_error(
                        HirPlaceResolutionErrorKind::InvalidSlice,
                        Some(index),
                        projection.span,
                    ));
                };
                if *element != indexed.element
                    || (*mutability == HirMutability::Mutable && !indexed.writable)
                {
                    return Err(place_error(
                        HirPlaceResolutionErrorKind::InvalidSlice,
                        Some(index),
                        projection.span,
                    ));
                }
                state.ty = projection.result_type;
                state.writable = *mutability == HirMutability::Mutable;
                state.downcast = None;
                state.required_alignment = indexed.alignment;
                state.static_offset_bytes = None;
                ResolvedHirProjectionKind::Slice {
                    start: start.as_deref(),
                    end: end.as_deref(),
                    bounds: indexed.bounds,
                    stride_bytes: indexed.stride_bytes,
                    mutability: *mutability,
                }
            }
            HirProjectionKind::Downcast { variant } => {
                let enum_layout = require_layout(program, state.ty, Some(index), projection.span)?;
                let valid_owner = state.downcast.is_none()
                    && matches!(
                        program.type_kind(state.ty),
                        Some(HirTypeKind::Enum { variants }) if variants.contains(variant)
                    )
                    && program
                        .variant(*variant)
                        .is_some_and(|definition| definition.owner == state.ty);
                let payload_offset_bytes = enum_layout
                    .variants
                    .as_ref()
                    .and_then(|layout| layout.cases.iter().find(|case| case.variant == *variant))
                    .map(|case| case.payload_offset_bytes)
                    .filter(|offset| *offset <= enum_layout.size_bytes);
                let Some(payload_offset_bytes) = payload_offset_bytes.filter(|_| valid_owner)
                else {
                    return Err(place_error(
                        HirPlaceResolutionErrorKind::InvalidDowncast,
                        Some(index),
                        projection.span,
                    ));
                };
                state.downcast = Some(*variant);
                state.static_offset_bytes = checked_static_add(
                    state.static_offset_bytes,
                    payload_offset_bytes,
                    index,
                    projection.span,
                )?;
                ResolvedHirProjectionKind::Downcast {
                    variant: *variant,
                    payload_offset_bytes,
                }
            }
        };
        if state.ty != projection.result_type {
            return Err(place_error(
                HirPlaceResolutionErrorKind::TypeMismatch,
                Some(index),
                projection.span,
            ));
        }
        projections.push(ResolvedHirProjection {
            kind: resolved_kind,
            input_type,
            output_type: state.ty,
            required_alignment: state.required_alignment,
            static_offset_bytes: state.static_offset_bytes,
            span: projection.span,
        });
    }

    if state.ty != place.ty {
        return Err(place_error(
            HirPlaceResolutionErrorKind::TypeMismatch,
            None,
            place.span,
        ));
    }
    if access == HirPlaceAccess::Write && !state.writable {
        return Err(place_error(
            HirPlaceResolutionErrorKind::ImmutableWrite,
            None,
            place.span,
        ));
    }
    Ok(ResolvedHirPlace {
        base: place.base,
        base_type,
        projections,
        ty: state.ty,
        writable: state.writable,
        required_alignment: state.required_alignment,
        static_offset_bytes: state.static_offset_bytes,
        span: place.span,
    })
}

#[derive(Clone, Copy)]
struct ResolutionState {
    ty: HirTypeId,
    writable: bool,
    downcast: Option<HirVariantId>,
    required_alignment: u64,
    static_offset_bytes: Option<u64>,
}

#[derive(Clone, Copy)]
struct IndexedType {
    element: HirTypeId,
    writable: bool,
    bounds: HirBoundsSource,
    stride_bytes: u64,
    alignment: u64,
}

fn indexed_type(
    program: &HirProgram,
    state: ResolutionState,
    projection_index: usize,
    span: ByteSpan,
) -> Result<IndexedType, HirPlaceResolutionError> {
    let (element, writable, bounds, array_length) = match program.type_kind(state.ty) {
        Some(HirTypeKind::Array { element, length }) => (
            *element,
            state.writable,
            HirBoundsSource::Array { length: *length },
            Some(*length),
        ),
        Some(HirTypeKind::Slice {
            element,
            mutability,
        }) => (
            *element,
            *mutability == HirMutability::Mutable,
            HirBoundsSource::Slice {
                slice_type: state.ty,
            },
            None,
        ),
        Some(HirTypeKind::Reference {
            pointee,
            mutability,
            ..
        }) => match program.type_kind(*pointee) {
            Some(HirTypeKind::Slice { element, .. }) => (
                *element,
                *mutability == HirMutability::Mutable,
                HirBoundsSource::Slice {
                    slice_type: state.ty,
                },
                None,
            ),
            _ => {
                return Err(place_error(
                    HirPlaceResolutionErrorKind::InvalidIndex,
                    Some(projection_index),
                    span,
                ));
            }
        },
        _ => {
            return Err(place_error(
                HirPlaceResolutionErrorKind::InvalidIndex,
                Some(projection_index),
                span,
            ));
        }
    };
    let element_layout = require_layout(program, element, Some(projection_index), span)?;
    let stride_bytes = align_up(
        element_layout.size_bytes,
        element_layout.alignment,
        projection_index,
        span,
    )?;
    if let Some(length) = array_length {
        let array_layout = require_layout(program, state.ty, Some(projection_index), span)?;
        if array_layout.alignment < element_layout.alignment {
            return Err(place_error(
                HirPlaceResolutionErrorKind::InvalidLayout,
                Some(projection_index),
                span,
            ));
        }
        let elements_size = stride_bytes.checked_mul(length).ok_or_else(|| {
            place_error(
                HirPlaceResolutionErrorKind::ArithmeticOverflow,
                Some(projection_index),
                span,
            )
        })?;
        let expected_size = align_up(
            elements_size,
            array_layout.alignment,
            projection_index,
            span,
        )?;
        if expected_size != array_layout.size_bytes {
            return Err(place_error(
                HirPlaceResolutionErrorKind::InvalidLayout,
                Some(projection_index),
                span,
            ));
        }
    }
    Ok(IndexedType {
        element,
        writable,
        bounds,
        stride_bytes,
        alignment: element_layout.alignment,
    })
}

fn tuple_element(
    program: &HirProgram,
    owner: HirTypeId,
    requested: u64,
    projection_index: usize,
    span: ByteSpan,
) -> Result<(HirTypeId, u64), HirPlaceResolutionError> {
    let Some(HirTypeKind::Tuple(elements)) = program.type_kind(owner) else {
        return Err(place_error(
            HirPlaceResolutionErrorKind::InvalidIndex,
            Some(projection_index),
            span,
        ));
    };
    let requested_index = usize::try_from(requested).map_err(|_| {
        place_error(
            HirPlaceResolutionErrorKind::InvalidIndex,
            Some(projection_index),
            span,
        )
    })?;
    let element = elements.get(requested_index).copied().ok_or_else(|| {
        place_error(
            HirPlaceResolutionErrorKind::InvalidIndex,
            Some(projection_index),
            span,
        )
    })?;
    let mut offset = 0u64;
    let mut aggregate_alignment = 1u64;
    for (position, candidate) in elements.iter().take(requested_index + 1).enumerate() {
        let layout = require_layout(program, *candidate, Some(projection_index), span)?;
        aggregate_alignment = aggregate_alignment.max(layout.alignment);
        offset = align_up(offset, layout.alignment, projection_index, span)?;
        if position == requested_index {
            break;
        }
        offset = offset.checked_add(layout.size_bytes).ok_or_else(|| {
            place_error(
                HirPlaceResolutionErrorKind::ArithmeticOverflow,
                Some(projection_index),
                span,
            )
        })?;
    }
    let owner_layout = require_layout(program, owner, Some(projection_index), span)?;
    let element_layout = require_layout(program, element, Some(projection_index), span)?;
    let end = offset.checked_add(element_layout.size_bytes);
    if owner_layout.alignment < aggregate_alignment
        || !end.is_some_and(|end| end <= owner_layout.size_bytes)
    {
        return Err(place_error(
            HirPlaceResolutionErrorKind::InvalidLayout,
            Some(projection_index),
            span,
        ));
    }
    Ok((element, offset))
}

fn field_offset(
    program: &HirProgram,
    owner_layout: &HirLayout,
    owner: HirTypeId,
    downcast: Option<HirVariantId>,
    field: HirFieldId,
    projection_index: usize,
    span: ByteSpan,
) -> Result<u64, HirPlaceResolutionError> {
    let field_definition = program.field(field).filter(|field| field.owner == owner);
    let offset = match program.type_kind(owner) {
        Some(HirTypeKind::Struct { fields }) if fields.contains(&field) => owner_layout
            .fields
            .iter()
            .find(|layout| layout.field == field)
            .map(|layout| layout.offset_bytes),
        Some(HirTypeKind::Enum { .. }) => downcast.and_then(|variant| {
            program
                .variant(variant)
                .filter(|variant| variant.owner == owner && variant.fields.contains(&field))?;
            owner_layout
                .variants
                .as_ref()?
                .cases
                .iter()
                .find(|case| case.variant == variant)?
                .fields
                .iter()
                .find(|layout| layout.field == field)
                .map(|layout| layout.offset_bytes)
        }),
        _ => None,
    };
    let (Some(field_definition), Some(offset)) = (field_definition, offset) else {
        return Err(place_error(
            HirPlaceResolutionErrorKind::InvalidField,
            Some(projection_index),
            span,
        ));
    };
    let field_layout = require_layout(program, field_definition.ty, Some(projection_index), span)?;
    let absolute_in_owner = match downcast {
        Some(variant) => owner_layout
            .variants
            .as_ref()
            .and_then(|layout| layout.cases.iter().find(|case| case.variant == variant))
            .and_then(|case| case.payload_offset_bytes.checked_add(offset)),
        None => Some(offset),
    };
    let end = absolute_in_owner.and_then(|offset| offset.checked_add(field_layout.size_bytes));
    if !absolute_in_owner.is_some_and(|offset| offset % field_layout.alignment == 0)
        || !end.is_some_and(|end| end <= owner_layout.size_bytes)
    {
        return Err(place_error(
            HirPlaceResolutionErrorKind::InvalidLayout,
            Some(projection_index),
            span,
        ));
    }
    Ok(offset)
}

fn access_alignment(
    program: &HirProgram,
    ty: HirTypeId,
    projection_index: Option<usize>,
    span: ByteSpan,
) -> Result<u64, HirPlaceResolutionError> {
    match program.type_kind(ty) {
        Some(HirTypeKind::Slice { element, .. }) => {
            Ok(require_layout(program, *element, projection_index, span)?.alignment)
        }
        Some(HirTypeKind::Reference { pointee, .. })
            if matches!(program.type_kind(*pointee), Some(HirTypeKind::Slice { .. })) =>
        {
            let Some(HirTypeKind::Slice { element, .. }) = program.type_kind(*pointee) else {
                unreachable!("guarded slice reference")
            };
            Ok(require_layout(program, *element, projection_index, span)?.alignment)
        }
        Some(_) => Ok(require_layout(program, ty, projection_index, span)?.alignment),
        None => Err(place_error(
            HirPlaceResolutionErrorKind::MissingType,
            projection_index,
            span,
        )),
    }
}

fn require_layout(
    program: &HirProgram,
    ty: HirTypeId,
    projection_index: Option<usize>,
    span: ByteSpan,
) -> Result<&HirLayout, HirPlaceResolutionError> {
    let definition = program.type_definition(ty).ok_or_else(|| {
        place_error(
            HirPlaceResolutionErrorKind::MissingType,
            projection_index,
            span,
        )
    })?;
    let layout_id = definition.layout.ok_or_else(|| {
        place_error(
            HirPlaceResolutionErrorKind::MissingLayout,
            projection_index,
            span,
        )
    })?;
    let layout = program
        .layout(layout_id)
        .filter(|layout| layout.ty == ty)
        .ok_or_else(|| {
            place_error(
                HirPlaceResolutionErrorKind::InvalidLayout,
                projection_index,
                span,
            )
        })?;
    if !layout.alignment.is_power_of_two() || layout.size_bytes % layout.alignment != 0 {
        return Err(place_error(
            HirPlaceResolutionErrorKind::InvalidLayout,
            projection_index,
            span,
        ));
    }
    Ok(layout)
}

fn align_up(
    value: u64,
    alignment: u64,
    projection_index: usize,
    span: ByteSpan,
) -> Result<u64, HirPlaceResolutionError> {
    if !alignment.is_power_of_two() {
        return Err(place_error(
            HirPlaceResolutionErrorKind::InvalidLayout,
            Some(projection_index),
            span,
        ));
    }
    value
        .checked_add(alignment - 1)
        .map(|value| value & !(alignment - 1))
        .ok_or_else(|| {
            place_error(
                HirPlaceResolutionErrorKind::ArithmeticOverflow,
                Some(projection_index),
                span,
            )
        })
}

fn checked_static_add(
    base: Option<u64>,
    offset: u64,
    projection_index: usize,
    span: ByteSpan,
) -> Result<Option<u64>, HirPlaceResolutionError> {
    base.map(|base| {
        base.checked_add(offset).ok_or_else(|| {
            place_error(
                HirPlaceResolutionErrorKind::ArithmeticOverflow,
                Some(projection_index),
                span,
            )
        })
    })
    .transpose()
}

const fn place_error(
    kind: HirPlaceResolutionErrorKind,
    projection_index: Option<usize>,
    span: ByteSpan,
) -> HirPlaceResolutionError {
    HirPlaceResolutionError {
        kind,
        projection_index,
        span,
    }
}
