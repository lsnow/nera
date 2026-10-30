//! Source qualification for new predicate arithmetic. Saved guarantees and
//! current observations may prove definedness, but the pending declaration
//! body never supplies premises for its own arguments or witness choices.
use super::*;

pub(super) struct ExpressionFacts<'a> {
    scope: InstanceScope,
    pub(super) saved: &'a [PredicateConstraintFact],
    scalars: BTreeMap<VirValueId, PredicateLogicValue>,
    pub(super) qualified: std::cell::RefCell<fact_inputs::QualifiedFacts<'a>>,
    scalars_projected: std::cell::Cell<bool>,
}

impl<'a> ExpressionFacts<'a> {
    pub(super) fn new(
        state: &'a ResourceState,
        scope: InstanceScope,
        saved: &'a [PredicateConstraintFact],
        arguments: &WitnessArguments<VirMemoryAccess, VirValueId>,
        inputs: &[PredicateLogicValue],
        budget: &mut LogicBudget,
    ) -> Result<Self, PredicateError> {
        if arguments.inputs.len() != inputs.len() {
            return Err(PredicateError::InvalidBinding);
        }
        let mut scalars = BTreeMap::new();
        for ((ty, input), value) in arguments.inputs.iter().zip(inputs) {
            budget.charge(1).map_err(map_error)?;
            if *ty != value.ty {
                return Err(PredicateError::InvalidBinding);
            }
            if let WitnessInput::Scalar(id) = input
                && scalars
                    .insert(*id, value.clone())
                    .is_some_and(|old| old != *value)
            {
                return Err(PredicateError::InvalidBinding);
            }
        }
        Ok(Self {
            scope,
            saved,
            scalars,
            qualified: std::cell::RefCell::new(fact_inputs::QualifiedFacts::new(
                state,
                Some(scope),
                saved,
            )),
            scalars_projected: std::cell::Cell::new(false),
        })
    }
}

impl ResourceState {
    #[expect(
        clippy::too_many_arguments,
        reason = "Keep boundary identities, state, evidence and shared budget explicit at the resource adapter"
    )]
    pub(super) fn evaluate_predicate_expression(
        &self,
        expression: &LogicExpression<VirMemoryAccess>,
        parameters: &[PredicateLogicValue],
        witnesses: &[PredicateLogicValue],
        context: &ExpressionFacts<'_>,
        observe: &mut impl FnMut(
            u32,
            u64,
            VirMemoryAccess,
            ObservationTime,
        ) -> Result<PredicateLogicValue, LogicError>,
        resource: &mut impl FnMut(u32, &[u64]) -> Result<PredicateLogicValue, LogicError>,
        capture: bool,
        budget: &mut LogicBudget,
    ) -> Result<PredicateLogicValue, PredicateError> {
        let plain = if capture {
            expression.evaluate_for_capture(parameters, witnesses, observe, resource, budget)
        } else {
            expression.evaluate(parameters, witnesses, observe, resource, budget)
        };
        match plain {
            Ok(value) => return Ok(value),
            Err(LogicError::Overflow) => {}
            Err(error) => return Err(map_error(error)),
        }
        // Resolve every leaf, then qualify the complete context before asking
        // the pure service to check every arithmetic intermediate in the DAG.
        let mut leaves = Vec::new();
        for (index, node) in expression.nodes.iter().enumerate() {
            budget.charge(1).map_err(map_error)?;
            if !matches!(
                node.kind,
                LogicNodeKind::Word(_)
                    | LogicNodeKind::Bool(_)
                    | LogicNodeKind::Binder(_)
                    | LogicNodeKind::Observe { .. }
                    | LogicNodeKind::Resource { .. }
            ) {
                continue;
            }
            let value = LogicExpression {
                nodes: vec![node.clone()],
                root: 0,
            }
            .evaluate_for_capture(parameters, witnesses, observe, resource, budget)
            .map_err(map_error)?;
            leaves.push((index as u32, value));
        }
        let mut queries = leaves
            .iter()
            .map(|(_, value)| value.clone())
            .collect::<Vec<_>>();
        // Real scalar slots remain useful even without a retained historical
        // origin. Never create such a slot for an opened or memory-only input.
        queries.extend(context.scalars.values().cloned());
        let mut qualified = context.qualified.borrow_mut();
        if !qualified.matches(self, context.scope, context.saved) {
            return Err(PredicateError::InvalidBinding);
        }
        let prepared = qualified.queries(&queries, budget)?;
        let facts = &mut qualified.facts;
        if !context.scalars_projected.get() {
            let actual = context
                .scalars
                .keys()
                .zip(&prepared[leaves.len()..])
                .filter_map(|(id, value)| value.clone().map(|value| (*id, value)))
                .collect();
            let differences = self.predicate_scalar_differences(&actual, budget)?;
            facts
                .extend_observations(&[], &differences, budget)
                .map_err(map_error)?;
            context.scalars_projected.set(true);
        }
        let leaves = leaves
            .into_iter()
            .zip(prepared)
            .map(|((id, value), prepared)| {
                // Unretained memory is a one-shot observation, not a saved
                // premise. Its current range can still check this operation.
                (id, Some(prepared.unwrap_or(value)))
            })
            .collect::<Vec<_>>();
        facts
            .evaluate_scalar(expression, &leaves, budget)
            .map_err(map_error)?
            .ok_or(PredicateError::UnprovedRepresentation)
    }
}

#[cfg(test)]
mod tests;
