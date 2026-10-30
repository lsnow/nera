//! Consume a checked slice's paired coordinates without inventing scalar SSA
//! values for pointer offsets. This only narrows address intervals; liveness,
//! initialization, authority and parent/child containment remain obligations.
use super::*;

pub(super) fn paired_source_bounds(
    state: &ResourceState,
    pointer: AbstractPointer,
    length_id: VirValueId,
    access: VirMemoryAccess,
    stride: u64,
) -> Option<(SymbolicRangeBound, SymbolicRangeBound)> {
    let AbstractValue::U64(length) = *state.value(length_id)? else {
        return None;
    };
    let footprint = pointer.slice_footprint()?;
    let (start, end) = footprint.range.bounds()?;
    if stride == 0
        || !matches!(pointer.provenance(), AbstractProvenance::Known(_))
        || footprint.provenance != pointer.provenance()
        || footprint.access != access
        || pointer.memory_access() != Some(access)
        || footprint.stride_bytes != stride
    {
        return None;
    }
    let base = pointer.offset_expression().or_else(|| {
        pointer
            .offset_bytes()
            .exact_value()
            .map(AffineExpression::constant)
    })?;
    if start.expression() != base {
        return None;
    }
    // Exact current values may have a canonical constant expression while the
    // checked return footprint retains the original SSA coordinate.
    let paired = [
        Some(AffineExpression::identity(length_id)),
        state.word_expression(length_id),
        length.exact_value().map(AffineExpression::constant),
    ]
    .into_iter()
    .flatten()
    .any(|length| {
        length
            .checked_scale(stride)
            .and_then(|n| base.checked_add(n))
            == Some(end.expression())
    });
    if !paired {
        return None;
    }
    let low_bytes = length.lower().checked_mul(stride)?;
    let high_bytes = length.upper().checked_mul(stride)?;
    let narrowed_start = start
        .interval()
        .intersection(pointer.offset_bytes())?
        .intersection(
            U64Interval::new(
                end.interval().lower().saturating_sub(high_bytes),
                end.interval().upper().checked_sub(low_bytes)?,
            )
            .ok()?,
        )?;
    let narrowed_end = end.interval().intersection(
        U64Interval::new(
            narrowed_start.lower().checked_add(low_bytes)?,
            narrowed_start.upper().checked_add(high_bytes)?,
        )
        .ok()?,
    )?;
    Some((
        SymbolicRangeBound::new(start.expression(), narrowed_start),
        SymbolicRangeBound::new(end.expression(), narrowed_end),
    ))
}

pub(super) fn coordinate_range(
    start: U64Interval,
    start_expression: Option<AffineExpression>,
    end: U64Interval,
    end_expression: Option<AffineExpression>,
) -> AbstractByteRange {
    match (start_expression, end_expression) {
        (Some(a), Some(b)) => AbstractByteRange::Symbolic {
            start: SymbolicRangeBound::new(a, start),
            end: SymbolicRangeBound::new(b, end),
        },
        _ => AbstractByteRange::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (ResourceState, AbstractPointer, VirValueId) {
        let id = VirValueId::new(0);
        let length = VirValueId::new(1);
        let provenance = AbstractProvenance::Known(AbstractAllocationId::External(0));
        let interval = U64Interval::new(8, 56).unwrap();
        let base = AffineExpression::identity(id);
        let range = coordinate_range(
            interval,
            Some(base),
            interval,
            base.checked_add(AffineExpression::identity(length).checked_scale(8).unwrap()),
        );
        let pointer =
            AbstractPointer::new(provenance, interval, GuaranteedAlignment::new(8).unwrap())
                .with_offset_expression(Some(base))
                .with_memory_access(Some(VirMemoryAccess::core_u64()))
                .with_domain(VirPointerDomain::Restricted(range))
                .with_slice_footprint(Some(MemoryFootprint {
                    provenance,
                    access: VirMemoryAccess::core_u64(),
                    stride_bytes: 8,
                    range,
                    envelope: ByteRange::new(8, 56).unwrap(),
                }));
        let mut state = ResourceState::new();
        state
            .define_value(id, AbstractValue::Pointer(pointer))
            .unwrap();
        state
            .define_value(length, AbstractValue::U64(U64Interval::exact(6)))
            .unwrap();
        (state, pointer, length)
    }

    #[test]
    fn paired_endpoint_narrows_offsets_without_replacing_symbolic_coordinates() {
        let (mut state, pointer, length) = fixture();
        let before = state.clone();
        let (start, end) =
            paired_source_bounds(&state, pointer, length, VirMemoryAccess::core_u64(), 8).unwrap();
        assert_eq!(start.interval(), U64Interval::exact(8));
        assert_eq!(end.interval(), U64Interval::exact(56));
        assert_eq!((start.expression(), end.expression()), {
            let (a, b) = pointer.slice_footprint().unwrap().range.bounds().unwrap();
            (a.expression(), b.expression())
        });
        assert_eq!(state, before);
        assert!(state.narrow_pointer_offset(VirValueId::new(0), start.interval()));
        let AbstractValue::Pointer(refined) = *state.value(VirValueId::new(0)).unwrap() else {
            panic!()
        };
        assert_eq!(refined.domain(), pointer.domain());
        assert_eq!(refined.slice_footprint(), pointer.slice_footprint());
        assert_eq!(refined.offset_expression(), pointer.offset_expression());
        assert_eq!(
            paired_source_bounds(&state, refined, length, VirMemoryAccess::core_u64(), 8),
            Some((start, end))
        );
        assert!(!state.narrow_pointer_offset(VirValueId::new(0), U64Interval::exact(9)));
    }

    #[test]
    fn equal_length_intervals_and_invalid_geometry_do_not_establish_a_pair() {
        let (mut state, pointer, length) = fixture();
        let other = VirValueId::new(2);
        state
            .define_value(other, AbstractValue::U64(U64Interval::exact(6)))
            .unwrap();
        assert!(
            paired_source_bounds(&state, pointer, other, VirMemoryAccess::core_u64(), 8).is_none()
        );
        assert!(
            paired_source_bounds(&state, pointer, length, VirMemoryAccess::core_u64(), 4).is_none()
        );
        assert!(
            paired_source_bounds(
                &state,
                pointer.with_slice_footprint(None),
                length,
                VirMemoryAccess::core_u64(),
                8
            )
            .is_none()
        );
        let footprint = pointer.slice_footprint().unwrap();
        let wrong = pointer.with_slice_footprint(Some(MemoryFootprint {
            provenance: AbstractProvenance::Known(AbstractAllocationId::External(1)),
            ..footprint
        }));
        assert!(
            paired_source_bounds(&state, wrong, length, VirMemoryAccess::core_u64(), 8).is_none()
        );
        *state.value_mut(length).unwrap() = AbstractValue::U64(U64Interval::exact(7));
        assert!(
            paired_source_bounds(&state, pointer, length, VirMemoryAccess::core_u64(), 8).is_none()
        );
    }
}
