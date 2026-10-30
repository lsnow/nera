//! Adapts already admitted predicate guarantees to typed memory cells.
//! Callers establish either an ABI premise or a checked induction premise.
//! No allocation, initialization, permission or scalar identity is created here.
use super::*;

impl ResourceState {
    pub(super) fn assume_predicate_scalar_bounds(
        &mut self,
        definition: &PredicateDefinition,
        allocations: &[AbstractAllocationId],
    ) -> Result<(), PredicateError> {
        if allocations.len() != definition.resources.len() {
            return Err(PredicateError::InvalidBinding);
        }
        for bound in &definition.scalar_constraints {
            let range = ByteRange::from_start_and_length(bound.offset_bytes, 8)
                .map_err(|_| PredicateError::InvalidDefinition)?;
            let allocation = self
                .allocations
                .get_mut(
                    allocations
                        .get(bound.resource)
                        .ok_or(PredicateError::InvalidDefinition)?,
                )
                .ok_or(PredicateError::MissingAuthority)?;
            if allocation.liveness() != LivenessState::Live
                || allocation.initialization().classify(range) != InitializationClass::Initialized
                || !allocation.valid_value_bytes().contains(range)
            {
                return Err(PredicateError::UnprovedRepresentation);
            }
            // Clauses on one typed cell are intersected, never overwritten by
            // the last clause. The loop head has already forgotten old values.
            let (lower, upper) = definition
                .scalar_constraints
                .iter()
                .filter(|other| {
                    other.resource == bound.resource
                        && other.offset_bytes == bound.offset_bytes
                        && other.access == bound.access
                })
                .fold((bound.lower, bound.upper), |(lower, upper), other| {
                    (lower.max(other.lower), upper.min(other.upper))
                });
            let declared =
                U64Interval::new(lower, upper).map_err(|_| PredicateError::InvalidDefinition)?;
            let value = match allocation.scalar_content(range, bound.access) {
                Some(AbstractValue::U64(actual)) => actual
                    .intersection(declared)
                    .ok_or(PredicateError::UnprovedRepresentation)?,
                Some(_) => return Err(PredicateError::InvalidBinding),
                None => declared,
            };
            let origin = allocation.scalar_origin(range, bound.access);
            allocation.record_scalar_content(range, bound.access, AbstractValue::U64(value));
            if let Some(origin) = origin {
                allocation.set_scalar_origin(range, bound.access, origin);
            }
        }
        Ok(())
    }
}
