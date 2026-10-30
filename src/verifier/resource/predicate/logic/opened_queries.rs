//! Qualify specification operands against their live opening actions before
//! combining package guarantees. This adapter supplies immutable facts; the
//! pure service neither selects holders nor inspects runtime resource state.
use super::*;

impl ResourceState {
    fn opened_query_witness(
        &self,
        action: u32,
        holder: u32,
        binder: u32,
    ) -> Result<(&PredicateInstance, PredicateLogicValue), PredicateError> {
        let instance = self
            .predicates
            .get(&PredicateHolder(holder))
            .ok_or(PredicateError::MissingHolder)?;
        if instance.folded
            || instance.opening_action != Some(action)
            || instance.logic_scope.is_none()
        {
            return Err(PredicateError::InvalidBinding);
        }
        let value = instance
            .logical_witnesses
            .get(binder as usize)
            .cloned()
            .ok_or(PredicateError::InvalidBinding)?;
        Ok((instance, value))
    }

    /// Both operands may come from different opened packages. Validate all
    /// actions first, then combine only the guarantees of those packages.
    /// Existentials retain their own scopes; only actual local scalar origins
    /// are expressed in common coordinates for this disposable query.
    pub(in crate::verifier) fn prove_opened_spec_comparison(
        &self,
        comparison: OpenedSpecComparison,
        left: OpenedSpecOperand,
        right: OpenedSpecOperand,
    ) -> Result<bool, PredicateError> {
        self.prove_opened_spec_comparison_with_budget(
            comparison,
            left,
            right,
            &mut LogicBudget::default(),
        )
    }

    fn prove_opened_spec_comparison_with_budget(
        &self,
        comparison: OpenedSpecComparison,
        left: OpenedSpecOperand,
        right: OpenedSpecOperand,
        budget: &mut LogicBudget,
    ) -> Result<bool, PredicateError> {
        self.prove_opened_spec_query_with_budget(
            comparison,
            &[
                OpenedSpecTerm::Operand(left),
                OpenedSpecTerm::Operand(right),
            ],
            0,
            1,
            budget,
        )
    }

    #[cfg(test)]
    pub(in crate::verifier) fn prove_opened_spec_query(
        &self,
        comparison: OpenedSpecComparison,
        terms: &[OpenedSpecTerm],
        left: u32,
        right: u32,
    ) -> Result<bool, PredicateError> {
        self.prove_opened_spec_query_with_budget(
            comparison,
            terms,
            left,
            right,
            &mut LogicBudget::default(),
        )
    }

    fn prove_opened_spec_query_with_budget(
        &self,
        comparison: OpenedSpecComparison,
        terms: &[OpenedSpecTerm],
        left: u32,
        right: u32,
        budget: &mut LogicBudget,
    ) -> Result<bool, PredicateError> {
        if terms.len() >= MAX_EXPRESSION_NODES {
            return Err(PredicateError::Budget);
        }
        let mut terms = terms.to_vec();
        terms.push(match comparison {
            OpenedSpecComparison::Equal => OpenedSpecTerm::Equal(left, right),
            OpenedSpecComparison::Less => OpenedSpecTerm::Less(left, right),
            OpenedSpecComparison::LessEqual => OpenedSpecTerm::LessEqual(left, right),
        });
        self.prove_opened_spec_formula_with_budget(&terms, terms.len() as u32 - 1, budget)
    }

    pub(in crate::verifier) fn prove_opened_spec_formula(
        &self,
        terms: &[OpenedSpecTerm],
        root: u32,
    ) -> Result<bool, PredicateError> {
        self.prove_opened_spec_formula_with_budget(terms, root, &mut LogicBudget::default())
    }

    fn prove_opened_spec_formula_with_budget(
        &self,
        terms: &[OpenedSpecTerm],
        root: u32,
        budget: &mut LogicBudget,
    ) -> Result<bool, PredicateError> {
        use crate::predicate_logic::query::{self, InputType};
        if terms.len() > MAX_EXPRESSION_NODES {
            return Err(PredicateError::Budget);
        }
        let mut sources = BTreeMap::new();
        let mut opened = BTreeMap::new();
        let mut input_types = BTreeMap::new();
        for (index, term) in terms.iter().enumerate() {
            budget.charge(1).map_err(map_error)?;
            let OpenedSpecTerm::Operand(operand) = *term else {
                continue;
            };
            let ty = match operand {
                OpenedSpecOperand::Opened {
                    action,
                    holder,
                    binder,
                } => {
                    let (instance, value) = self.opened_query_witness(action, holder, binder)?;
                    let ty = match value.ty {
                        LogicType::U64 => InputType::U64,
                        LogicType::Usize => InputType::Usize,
                        LogicType::Bool => InputType::Bool,
                        _ => return Err(PredicateError::InvalidBinding),
                    };
                    sources.insert(PredicateHolder(holder), instance);
                    opened.insert(index as u32, value);
                    ty
                }
                OpenedSpecOperand::Word(_) => InputType::Word,
                OpenedSpecOperand::Bool(_) => InputType::Bool,
                OpenedSpecOperand::Value(id) => match self.value(id) {
                    Some(AbstractValue::U64(_)) => InputType::Word,
                    Some(AbstractValue::Bool(_)) => InputType::Bool,
                    _ => return Err(PredicateError::InvalidBinding),
                },
            };
            input_types.insert(index as u32, ty);
        }
        let query = query::elaborate::<VirMemoryAccess, _>(terms, root, &input_types, budget)
            .map_err(|error| match error {
                LogicError::Budget => PredicateError::Budget,
                _ => PredicateError::InvalidBinding,
            })?;
        let Some((_, anchor)) = sources.first_key_value() else {
            return Ok(false);
        };
        let scope = anchor.logic_scope.ok_or(PredicateError::InvalidBinding)?;
        let mut queries = Vec::new();
        for (node, original) in &query.operands {
            let ty = query.expression.nodes[*node as usize].ty;
            let value = match terms[*original as usize] {
                OpenedSpecTerm::Operand(OpenedSpecOperand::Opened { .. }) => opened
                    .get(original)
                    .cloned()
                    .ok_or(PredicateError::InvalidBinding)?,
                OpenedSpecTerm::Operand(OpenedSpecOperand::Word(n)) => TypedLogicValue {
                    ty,
                    value: LogicValue::Word(AffineValue::exact(n)),
                },
                OpenedSpecTerm::Operand(OpenedSpecOperand::Bool(b)) => TypedLogicValue {
                    ty,
                    value: LogicValue::Bool(Some(b)),
                },
                OpenedSpecTerm::Operand(OpenedSpecOperand::Value(id)) => {
                    self.predicate_scalar_input(scope, ty, id, &anchor.logical_local_aliases)?
                }
                _ => return Err(PredicateError::InvalidBinding),
            };
            queries.push(value);
        }
        let mut snapshots = Vec::new();
        for instance in sources.values() {
            if snapshots.len() + instance.logical_facts.len() > MAX_CONSTRAINTS {
                return Err(PredicateError::Budget);
            }
            budget
                .charge(instance.logical_facts.len())
                .map_err(map_error)?;
            snapshots.extend_from_slice(&instance.logical_facts);
        }
        let (mut facts, inputs) = self.established_constraint_facts_with_inputs(
            &snapshots,
            &queries,
            Some(scope),
            budget,
        )?;
        // One erased runtime slot may occur in independent nominal domains.
        // Project each typed view separately instead of overwriting by slot id.
        for ty in [LogicType::U64, LogicType::Usize] {
            let actual = query
                .operands
                .iter()
                .zip(&inputs)
                .filter_map(|((_, original), value)| {
                    let OpenedSpecTerm::Operand(OpenedSpecOperand::Value(id)) =
                        terms[*original as usize]
                    else {
                        return None;
                    };
                    value
                        .as_ref()
                        .filter(|value| value.ty == ty)
                        .cloned()
                        .map(|value| (id, value))
                })
                .collect::<BTreeMap<_, _>>();
            if !actual.is_empty() {
                let differences = self.predicate_scalar_differences(&actual, budget)?;
                facts
                    .extend_observations(&[], &differences, budget)
                    .map_err(map_error)?;
            }
        }
        let leaves = query
            .operands
            .into_iter()
            .zip(inputs)
            .map(|((node, _), value)| (node, value))
            .collect::<Vec<_>>();
        facts
            .proves(&query.expression, &leaves, budget)
            .map_err(map_error)
    }
}

#[cfg(test)]
mod tests;
