//! Actual argument evaluation. Plain evaluation is the fast path; a scalar whose
//! domain needs relations is checked as a complete source DAG by the pure
//! service, including every intermediate. No declaration guarantee is assumed.
use super::*;

impl ResourceState {
    pub(super) fn evaluate_predicate_arguments(
        &self,
        logic: &PredicateLogic<VirMemoryAccess>,
        arguments: &WitnessArguments<VirMemoryAccess, VirValueId>,
        inputs: &[PredicateLogicValue],
        context: &ExpressionFacts<'_>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<PredicateLogicValue>, PredicateError> {
        if arguments.arguments.len() != logic.parameters.len()
            || arguments.arguments.len() > MAX_LOGIC_PARAMETERS
            || arguments.inputs.len() != inputs.len()
        {
            return Err(PredicateError::InvalidBinding);
        }
        arguments
            .arguments
            .iter()
            .zip(&logic.parameters)
            .map(|(expr, parameter)| {
                let value = self.evaluate_predicate_expression(
                    expr,
                    inputs,
                    &[],
                    context,
                    &mut |_, _, _, _| Err(LogicError::Unbound),
                    &mut |_, _| Err(LogicError::Unbound),
                    true,
                    budget,
                )?;
                if value.ty != parameter.ty {
                    return Err(PredicateError::InvalidBinding);
                }
                Ok(value)
            })
            .collect()
    }
}
