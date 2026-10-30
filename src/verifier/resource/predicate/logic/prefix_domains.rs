//! Actual-domain admission after a count-to-source identity was established.
//! Only checked contract imports call this adapter; arithmetic preimages alone
//! never justify initialized storage or resource authority.
use super::*;

impl ResourceState {
    pub(super) fn refine_imported_prefix_domain(
        &mut self,
        expression: AffineExpression,
        count: &AffineValue<ObservationAtom>,
        length: u64,
        budget: &mut LogicBudget,
    ) -> Result<(), PredicateError> {
        let operands = expression
            .terms()
            .into_iter()
            .flatten()
            .map(|(id, scale)| {
                let Some(AbstractValue::U64(actual)) = self.value(id) else {
                    return Err(PredicateError::InvalidBinding);
                };
                Ok((id, (scale, actual.lower(), actual.upper())))
            })
            .collect::<Result<Vec<_>, PredicateError>>()?;
        let projected = crate::predicate_logic::affine::positive_affine_projection(
            expression.addend(),
            &operands.iter().map(|(_, term)| *term).collect::<Vec<_>>(),
            count.lower,
            count.upper,
            budget,
        )
        .map_err(map_error)?;
        for ((id, _), (lower, upper)) in operands.into_iter().zip(projected) {
            let narrowed = U64Interval::new(lower, upper)
                .map_err(|_| PredicateError::UnprovedRepresentation)?;
            // Monotone refinement preserves immutable histories and existing
            // initialization dependencies; replacing the value would erase them.
            self.narrow_word_interval(id, narrowed);
        }
        // Independent projected intervals do not preserve joint correlations.
        // Admit only when these actual intervals prove the complete endpoint.
        let actual = expression
            .interval(|id| match self.value(id) {
                Some(AbstractValue::U64(value)) => Some(*value),
                _ => None,
            })
            .ok_or(PredicateError::UnprovedRepresentation)?;
        if actual.upper() > length {
            return Err(PredicateError::UnprovedRepresentation);
        }
        Ok(())
    }
}
