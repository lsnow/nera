//! Existing numeric fast paths, moved without changing their verdict rules.
use super::super::{
    AbstractAllocation, AbstractPointer, AbstractProvenance, AffineExpression, ObligationStatus,
    SymbolicRangeBound, U64Interval,
};

pub(in crate::verifier) fn object_non_overlap_status(
    destination: AbstractPointer,
    source: AbstractPointer,
    size_bytes: u64,
) -> ObligationStatus {
    if size_bytes == 0 {
        return ObligationStatus::Proven;
    }
    match (destination.provenance(), source.provenance()) {
        (AbstractProvenance::Known(left), AbstractProvenance::Known(right)) if left != right => {
            return ObligationStatus::Proven;
        }
        (AbstractProvenance::Known(_), AbstractProvenance::Known(_)) => {}
        _ => return ObligationStatus::Unknown,
    }

    let destination_start =
        symbolic_bound(destination.offset_bytes(), destination.offset_expression());
    let source_start = symbolic_bound(source.offset_bytes(), source.offset_expression());
    let (destination_before_source, source_before_destination) =
        if let (Some(destination_start), Some(source_start)) = (destination_start, source_start) {
            (
                destination_start
                    .checked_add_constant(size_bytes)
                    .map_or(ObligationStatus::Unknown, |end| {
                        bound_le_status(end, source_start)
                    }),
                source_start
                    .checked_add_constant(size_bytes)
                    .map_or(ObligationStatus::Unknown, |end| {
                        bound_le_status(end, destination_start)
                    }),
            )
        } else {
            let destination_end = add_constant_interval(destination.offset_bytes(), size_bytes);
            let source_end = add_constant_interval(source.offset_bytes(), size_bytes);
            (
                destination_end.map_or(ObligationStatus::Unknown, |end| {
                    interval_le_status(end, source.offset_bytes())
                }),
                source_end.map_or(ObligationStatus::Unknown, |end| {
                    interval_le_status(end, destination.offset_bytes())
                }),
            )
        };
    if destination_before_source.is_proven() || source_before_destination.is_proven() {
        ObligationStatus::Proven
    } else if destination_before_source == ObligationStatus::Refuted
        && source_before_destination == ObligationStatus::Refuted
    {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

pub(in crate::verifier) fn add_constant_interval(
    interval: U64Interval,
    value: u64,
) -> Option<U64Interval> {
    U64Interval::new(
        interval.lower().checked_add(value)?,
        interval.upper().checked_add(value)?,
    )
    .ok()
}

pub(in crate::verifier) fn add_pointer_intervals(
    base: U64Interval,
    delta: U64Interval,
) -> (U64Interval, ObligationStatus) {
    let lower = base.lower().checked_add(delta.lower());
    let upper = base.upper().checked_add(delta.upper());
    match (lower, upper) {
        (Some(lower), Some(upper)) => (
            U64Interval::new(lower, upper).unwrap_or_else(|_| U64Interval::unknown()),
            ObligationStatus::Proven,
        ),
        (None, _) => (U64Interval::unknown(), ObligationStatus::Refuted),
        (Some(_), None) => (U64Interval::unknown(), ObligationStatus::Unknown),
    }
}

pub(in crate::verifier) fn scale_pointer_interval(
    value: U64Interval,
    factor: u64,
) -> (U64Interval, ObligationStatus) {
    let lower = value.lower().checked_mul(factor);
    let upper = value.upper().checked_mul(factor);
    match (lower, upper) {
        (Some(lower), Some(upper)) => (
            U64Interval::new(lower, upper).unwrap_or_else(|_| U64Interval::unknown()),
            ObligationStatus::Proven,
        ),
        (None, _) => (U64Interval::unknown(), ObligationStatus::Refuted),
        (Some(_), None) => (U64Interval::unknown(), ObligationStatus::Unknown),
    }
}

pub(in crate::verifier) fn object_bounds_status(
    offset: U64Interval,
    object_bytes: u64,
    size_bytes: u64,
) -> ObligationStatus {
    let minimum_end = offset.lower().checked_add(object_bytes);
    let maximum_end = offset.upper().checked_add(object_bytes);
    match (minimum_end, maximum_end) {
        (None, _) => ObligationStatus::Refuted,
        (Some(minimum), _) if minimum > size_bytes => ObligationStatus::Refuted,
        (_, Some(maximum)) if maximum <= size_bytes => ObligationStatus::Proven,
        _ => ObligationStatus::Unknown,
    }
}

pub(in crate::verifier) fn object_alignment_status(
    pointer: AbstractPointer,
    allocation: &AbstractAllocation,
    required_alignment: u64,
) -> ObligationStatus {
    if allocation.alignment().bytes() < required_alignment {
        return ObligationStatus::Refuted;
    }
    if pointer.alignment().bytes() >= required_alignment {
        return ObligationStatus::Proven;
    }
    if pointer
        .offset_bytes()
        .exact_value()
        .is_some_and(|offset| offset % required_alignment != 0)
    {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

pub(in crate::verifier) fn symbolic_bound(
    interval: U64Interval,
    expression: Option<AffineExpression>,
) -> Option<SymbolicRangeBound> {
    expression
        .map(|expression| SymbolicRangeBound::new(expression, interval))
        .or_else(|| interval.exact_value().map(SymbolicRangeBound::constant))
}

pub(in crate::verifier) fn bound_le_status(
    left: SymbolicRangeBound,
    right: SymbolicRangeBound,
) -> ObligationStatus {
    let left_expression = left.expression();
    let right_expression = right.expression();
    if left_expression == right_expression {
        return ObligationStatus::Proven;
    }
    if left_expression.same_terms(right_expression) {
        return if left_expression.addend() <= right_expression.addend() {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Refuted
        };
    }
    interval_le_status(left.interval(), right.interval())
}

pub(in crate::verifier) fn interval_le_status(
    left: U64Interval,
    right: U64Interval,
) -> ObligationStatus {
    if left.upper() <= right.lower() {
        ObligationStatus::Proven
    } else if left.lower() > right.upper() {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

pub(in crate::verifier) fn interval_lt_status(
    left: U64Interval,
    right: U64Interval,
) -> ObligationStatus {
    if left.upper() < right.lower() {
        ObligationStatus::Proven
    } else if left.lower() >= right.upper() {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn classified(values: impl IntoIterator<Item = bool>) -> ObligationStatus {
        let values = values.into_iter().collect::<Vec<_>>();
        if values.iter().all(|value| *value) {
            ObligationStatus::Proven
        } else if values.iter().all(|value| !*value) {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        }
    }

    #[test]
    fn interval_comparison_matches_independent_finite_universal_oracle() {
        for low_a in 0..5 {
            for high_a in low_a..5 {
                for low_b in 0..5 {
                    for high_b in low_b..5 {
                        let a = U64Interval::new(low_a, high_a).unwrap();
                        let b = U64Interval::new(low_b, high_b).unwrap();
                        let pairs =
                            || (low_a..=high_a).flat_map(|x| (low_b..=high_b).map(move |y| (x, y)));
                        assert_eq!(
                            interval_lt_status(a, b),
                            classified(pairs().map(|(x, y)| x < y))
                        );
                        assert_eq!(
                            interval_le_status(a, b),
                            classified(pairs().map(|(x, y)| x <= y))
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn overflow_classification_matches_wide_arithmetic_without_assuming_safety() {
        for start in [0, 1, u64::MAX / 2, u64::MAX - 2] {
            let end = start + 2;
            let interval = U64Interval::new(start, end).unwrap();
            for factor in [0, 1, 2, u64::MAX] {
                assert_eq!(
                    scale_pointer_interval(interval, factor).1,
                    classified(
                        (start..=end)
                            .map(|x| u128::from(x) * u128::from(factor) <= u128::from(u64::MAX))
                    )
                );
                assert_eq!(
                    add_pointer_intervals(interval, U64Interval::exact(factor)).1,
                    classified(
                        (start..=end)
                            .map(|x| u128::from(x) + u128::from(factor) <= u128::from(u64::MAX))
                    )
                );
            }
        }
    }
}
