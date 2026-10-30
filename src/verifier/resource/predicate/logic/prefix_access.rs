//! Read-only adaptation of an actual memory range to established logical
//! initialization. Pure entailment receives scalar endpoints, never authority.
use super::*;
use crate::predicate_logic::facts::Comparison;

impl ResourceState {
    /// This only enables a bounded mapping attempt. The eventual range query
    /// and ordinary authority checks must still establish the actual call.
    pub(in crate::verifier) fn has_logical_initialization(
        &self,
        allocation: AbstractAllocationId,
    ) -> bool {
        let Some(storage) = self.allocation(allocation) else {
            return false;
        };
        storage.liveness() == LivenessState::Live
            && self.predicates.values().any(|instance| {
                instance.logical_initialization.iter().any(|fact| {
                    fact.allocation == allocation
                        && Some(fact.revision) == storage.initialization_revision
                })
            })
    }

    pub(in crate::verifier::resource) fn logical_initialized_prefix_covers(
        &self,
        allocation: AbstractAllocationId,
        access: VirMemoryAccess,
        range: AbstractByteRange,
    ) -> bool {
        self.logical_prefix_access(allocation, access, range, &mut LogicBudget::default())
            == Ok(true)
    }

    pub(in crate::verifier::resource::predicate) fn logical_prefix_access(
        &self,
        allocation: AbstractAllocationId,
        access: VirMemoryAccess,
        range: AbstractByteRange,
        budget: &mut LogicBudget,
    ) -> Result<bool, PredicateError> {
        let Some(storage) = self.allocation(allocation) else {
            return Ok(false);
        };
        if storage.liveness() != LivenessState::Live {
            return Ok(false);
        }
        let Some((begin, end)) = range.bounds() else {
            return Ok(false);
        };
        // All candidate certificates share this budget, including failed
        // entailments. A later package cannot reset an exhausted query.
        for instance in self.predicates.values() {
            budget.charge(1).map_err(map_error)?;
            let Some(scope) = instance.logic_scope else {
                continue;
            };
            for fact in &instance.logical_initialization {
                budget.charge(1).map_err(map_error)?;
                if fact.allocation != allocation
                    || fact.element != access
                    || Some(fact.revision) != storage.initialization_revision
                {
                    continue;
                }
                let extent = fact
                    .length
                    .checked_mul(fact.stride)
                    .and_then(|n| fact.array_offset.checked_add(n))
                    .ok_or(PredicateError::InvalidDefinition)?;
                if extent > storage.size_bytes() {
                    continue;
                }
                let LogicValue::Word(count) = &fact.count.value else {
                    return Err(PredicateError::InvalidBinding);
                };
                // Exact element coordinates avoid introducing byte-scale
                // arithmetic into the logical count. A partial or misaligned
                // element is not admitted by this typed prefix adapter.
                let coordinate = |bound: SymbolicRangeBound| {
                    bound
                        .expression()
                        .checked_sub_constant(fact.array_offset)?
                        .checked_div_exact(fact.stride)
                };
                let (Some(begin), Some(end)) = (coordinate(begin), coordinate(end)) else {
                    continue;
                };
                let lower = self.prefix_expression_value(begin, scope)?;
                let upper = self.prefix_expression_value(end, scope)?;
                // Qualify the complete context once. All three ordered
                // endpoints use the same facts and budget, rather than
                // rebuilding the source observations for each comparison.
                let queries = [AffineValue::exact(0), lower, upper, count.clone()].map(|word| {
                    TypedLogicValue {
                        ty: LogicType::Usize,
                        value: LogicValue::Word(word),
                    }
                });
                let (facts, inputs) = self.established_constraint_facts_with_inputs(
                    &instance.logical_facts,
                    &queries,
                    instance.logic_scope,
                    budget,
                )?;
                let [Some(zero), Some(lower), Some(upper), Some(count)] = inputs.as_slice() else {
                    continue;
                };
                if facts
                    .entails(Comparison::LessEqual, zero, lower, budget)
                    .map_err(map_error)?
                    && facts
                        .entails(Comparison::LessEqual, lower, upper, budget)
                        .map_err(map_error)?
                    && facts
                        .entails(Comparison::LessEqual, upper, count, budget)
                        .map_err(map_error)?
                {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }
}
