//! Re-evaluate checked byte coordinates in their current SSA state. A pointer
//! root denotes only its allocation-relative offset, never a U64 program value.
use super::*;
use crate::{AbstractProvenance, AbstractValue, AffineExpression};

pub(super) fn refine_pair(
    state: &ResourceState,
    left: SymbolicRangeBound,
    right: SymbolicRangeBound,
    limits: DifferenceLimits,
) -> Result<Option<(SymbolicRangeBound, SymbolicRangeBound)>, DifferenceStop> {
    let roots = [left, right]
        .into_iter()
        .flat_map(|bound| {
            bound
                .expression()
                .terms()
                .into_iter()
                .flatten()
                .map(|(id, _)| id)
        })
        .collect::<std::collections::BTreeSet<_>>();
    if !roots
        .iter()
        .any(|id| matches!(state.value(*id), Some(AbstractValue::Pointer(_))))
    {
        return Ok(None);
    }
    if roots.len() > limits.max_variables || limits.max_steps < 4 + roots.len() {
        return Err(DifferenceStop::Budget);
    }
    let evaluate = |bound: SymbolicRangeBound| -> Result<SymbolicRangeBound, DifferenceStop> {
        let actual = bound
            .expression()
            .interval(|id| match state.value(id)? {
                AbstractValue::U64(value) => Some(*value),
                AbstractValue::Pointer(pointer)
                    if matches!(pointer.provenance(), AbstractProvenance::Known(_))
                        && pointer.memory_access().is_some()
                        && pointer.offset_expression() == Some(AffineExpression::identity(id)) =>
                {
                    Some(pointer.offset_bytes())
                }
                _ => None,
            })
            .ok_or(DifferenceStop::InvalidInput)?;
        let interval = bound
            .interval()
            .intersection(actual)
            .ok_or(DifferenceStop::Inconsistent)?;
        Ok(SymbolicRangeBound::new(bound.expression(), interval))
    };
    // An unavailable coordinate contributes no new premise. Inconsistency and
    // exhausted bounds must still fail closed instead of choosing one copy.
    match (evaluate(left), evaluate(right)) {
        (Ok(a), Ok(b)) => Ok(Some((a, b))),
        (Err(DifferenceStop::Inconsistent), _) | (_, Err(DifferenceStop::Inconsistent)) => {
            Err(DifferenceStop::Inconsistent)
        }
        _ => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AbstractAllocationId, GuaranteedAlignment, VirMemoryAccess, VirValueId};

    fn fixture() -> (ResourceState, SymbolicRangeBound, SymbolicRangeBound) {
        let pointer_id = VirValueId::new(0);
        let length_id = VirValueId::new(1);
        let expression = AffineExpression::identity(pointer_id);
        let pointer = AbstractPointer::new(
            AbstractProvenance::Known(AbstractAllocationId::External(0)),
            U64Interval::exact(8),
            GuaranteedAlignment::new(8).unwrap(),
        )
        .with_memory_access(Some(VirMemoryAccess::core_u64()))
        .with_offset_expression(Some(expression));
        let mut state = ResourceState::new();
        state
            .define_value(pointer_id, AbstractValue::Pointer(pointer))
            .unwrap();
        state
            .define_value(length_id, AbstractValue::U64(U64Interval::exact(6)))
            .unwrap();
        let broad = U64Interval::new(8, 56).unwrap();
        (
            state,
            SymbolicRangeBound::new(expression, broad),
            SymbolicRangeBound::new(
                expression
                    .checked_add(
                        AffineExpression::identity(length_id)
                            .checked_scale(8)
                            .unwrap(),
                    )
                    .unwrap(),
                broad,
            ),
        )
    }

    #[test]
    fn current_offset_bounds_are_address_evidence_not_scalar_premises() {
        let (state, start, end) = fixture();
        let before = state.clone();
        for (a, b) in [
            (start, SymbolicRangeBound::constant(8)),
            (SymbolicRangeBound::constant(16), end),
        ] {
            let proof = ordered(&state, a, b, DifferenceLimits::default());
            assert_eq!(proof.status, S::Proven);
            assert!(proof.coordinates.is_some());
            assert!(proof.difference.is_none());
        }
        assert_eq!(local::interval(&state, word(VirValueId::new(0))), None);
        assert_eq!(state, before);
    }

    #[test]
    fn missing_foreign_and_inconsistent_coordinates_fail_closed() {
        let (state, start, end) = fixture();
        for mutation in 0..3 {
            let mut changed = state.clone();
            let AbstractValue::Pointer(pointer) = *changed.value(VirValueId::new(0)).unwrap()
            else {
                panic!()
            };
            *changed.value_mut(VirValueId::new(0)).unwrap() =
                match mutation {
                    0 => AbstractValue::U64(U64Interval::unknown()),
                    1 => AbstractValue::Pointer(pointer.with_offset_expression(Some(
                        AffineExpression::identity(VirValueId::new(99)),
                    ))),
                    _ => AbstractValue::Pointer(AbstractPointer::new(
                        AbstractProvenance::Unknown,
                        U64Interval::exact(8),
                        pointer.alignment(),
                    )),
                };
            assert_ne!(
                ordered(
                    &changed,
                    start,
                    SymbolicRangeBound::constant(8),
                    DifferenceLimits::default()
                )
                .status,
                S::Proven
            );
        }
        let limits = DifferenceLimits {
            max_steps: 0,
            ..DifferenceLimits::default()
        };
        let proof = ordered(&state, start, SymbolicRangeBound::constant(8), limits);
        assert_eq!(proof.status, S::Unknown);
        assert_eq!(proof.stop, Some(DifferenceStop::Budget));
        let impossible =
            SymbolicRangeBound::new(end.expression(), U64Interval::new(8, 55).unwrap());
        assert_eq!(
            refine_pair(&state, start, impossible, DifferenceLimits::default()),
            Err(DifferenceStop::Inconsistent)
        );
    }
}
