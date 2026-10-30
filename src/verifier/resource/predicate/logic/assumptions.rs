//! Facts about an existential package are qualified by the actual values of
//! every leaf. Reusing a declaration or a byte address cannot reuse a fact.
use super::*;

pub(super) fn reusable_leaf(
    value: &PredicateLogicValue,
    budget: &mut LogicBudget,
) -> Result<bool, PredicateError> {
    let stable = |atom: &ObservationAtom| !matches!(atom, ObservationAtom::Memory { .. });
    let leaves = value.value.capture_leaves(budget).map_err(map_error)?;
    Ok(leaves.into_iter().all(|leaf| match leaf {
        LogicValue::Word(word) => word.terms.keys().all(stable),
        LogicValue::BoolAtom { atom, .. } => stable(atom),
        LogicValue::BoolComparison { left, right, .. } => {
            left.terms.keys().chain(right.terms.keys()).all(stable)
        }
        _ => true,
    }))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::verifier::resource) struct PredicateConstraintFact {
    pub(super) expression: LogicExpression<VirMemoryAccess>,
    pub(super) leaves: Vec<(u32, PredicateLogicValue)>,
}

impl ResourceState {
    /// Argument matching may use an established scalar equality, but never
    /// treats equal addresses or equal ranges as interchangeable authority.
    pub(in crate::verifier::resource::predicate) fn predicate_argument_equality(
        &self,
        instance: &PredicateInstance,
        left: PredicateLogicValue,
        right: PredicateLogicValue,
        budget: &mut LogicBudget,
    ) -> Result<bool, PredicateError> {
        if left.ty != right.ty {
            return Ok(false);
        }
        // Reconcile actual copies before even the symbolic equality fast path:
        // singleton observations now retain their atoms, so shape equality must
        // not bypass a conflicting live alias.
        let left = self.refine_local_capture(instance, left, budget)?;
        let right = self.refine_local_capture(instance, right, budget)?;
        // Query reductions are disposable: retain the captures for the mixed
        // facts fallback, where their numeric operands must remain available.
        let reduced_left = self.refine_predicate_boolean(left.clone());
        let reduced_right = self.refine_predicate_boolean(right.clone());
        let equal = match (&reduced_left.value, &reduced_right.value) {
            (LogicValue::Word(a), LogicValue::Word(b)) => a.equal(b),
            (
                a @ (LogicValue::Bool(_)
                | LogicValue::BoolAtom { .. }
                | LogicValue::BoolComparison { .. }
                | LogicValue::BoolBinary { .. }),
                b @ (LogicValue::Bool(_)
                | LogicValue::BoolAtom { .. }
                | LogicValue::BoolComparison { .. }
                | LogicValue::BoolBinary { .. }),
            ) => a.bool_equal(b),
            _ => None,
        };
        if let Some(equal) = equal {
            return Ok(equal);
        }
        let scope = instance.logic_scope;
        let (facts, inputs) = self.established_constraint_facts_with_inputs(
            &instance.logical_facts,
            &[left, right],
            scope,
            budget,
        )?;
        let [Some(left), Some(right)] = inputs.as_slice() else {
            return Ok(false);
        };
        facts
            .entails(
                crate::predicate_logic::facts::Comparison::Equal,
                left,
                right,
                budget,
            )
            .map_err(map_error)
    }

    /// Resolve all established and query leaves together. The queries supply
    /// actual observation coordinates, never their proposed Boolean truth.
    /// Clause guarantees are imported only from the saved snapshot list.
    pub(super) fn established_constraint_facts_with_inputs(
        &self,
        snapshots: &[PredicateConstraintFact],
        queries: &[PredicateLogicValue],
        scope: Option<InstanceScope>,
        budget: &mut LogicBudget,
    ) -> Result<(fact_inputs::Facts, Vec<Option<PredicateLogicValue>>), PredicateError> {
        let mut context = fact_inputs::QualifiedFacts::new(self, scope, snapshots);
        let prepared = context.queries(queries, budget)?;
        Ok((context.facts, prepared))
    }

    /// Project consequences of saved guarantees without creating an SSA root
    /// for hidden values or equating observations by their abstract intervals.
    pub(super) fn bounded_opened_witness(
        &self,
        instance: &PredicateInstance,
        target: PredicateLogicValue,
        budget: &mut LogicBudget,
    ) -> Result<PredicateLogicValue, PredicateError> {
        if !reusable_leaf(&target, budget)? {
            return Ok(target);
        }
        let (facts, mut inputs) = self.established_constraint_facts_with_inputs(
            &instance.logical_facts,
            std::slice::from_ref(&target),
            None,
            budget,
        )?;
        let Some(target) = inputs.remove(0) else {
            return Ok(target);
        };
        facts.refine(target, budget).map_err(map_error)
    }

    pub(super) fn import_predicate_witnesses(
        &self,
        definition: &PredicateDefinition,
        parameters: &[PredicateLogicValue],
        scope: InstanceScope,
        observe: &mut impl FnMut(
            u32,
            u64,
            VirMemoryAccess,
            ObservationTime,
        ) -> Result<PredicateLogicValue, LogicError>,
        resource: &mut impl FnMut(u32, &[u64]) -> Result<PredicateLogicValue, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<PredicateLogicValue>, PredicateError> {
        if definition.logic.existentials.len() > MAX_EXISTENTIALS {
            return Err(PredicateError::Budget);
        }
        let mut witnesses = Vec::new();
        for (binder, declaration) in definition.logic.existentials.iter().enumerate() {
            budget.charge(1).map_err(map_error)?;
            let value = if definition.projected_witnesses.contains(&(binder as u32)) {
                declaration
                    .default
                    .as_ref()
                    .ok_or(PredicateError::InvalidDefinition)?
                    .evaluate(parameters, &witnesses, observe, resource, budget)
                    .map_err(map_error)?
            } else {
                let atom = ObservationAtom::Existential {
                    scope,
                    binder: binder as u32,
                };
                let value = match declaration.ty {
                    LogicType::U64 | LogicType::Usize => LogicValue::Word(
                        AffineValue::variable(atom, 0, u64::MAX).map_err(map_error)?,
                    ),
                    LogicType::Bool => LogicValue::BoolAtom {
                        atom,
                        negated: false,
                        known: None,
                    },
                    LogicType::Resource(_) => LogicValue::ResourceAtom { atom },
                };
                TypedLogicValue {
                    ty: declaration.ty,
                    value,
                }
            };
            if value.ty != declaration.ty {
                return Err(PredicateError::InvalidDefinition);
            }
            witnesses.push(value);
        }
        Ok(witnesses)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Keep boundary identities, state, evidence and shared budget explicit at the resource adapter"
    )]
    fn predicate_constraint_snapshot(
        &self,
        definition: &PredicateDefinition,
        resources: &[SealedResource],
        scope: InstanceScope,
        parameters: &[PredicateLogicValue],
        witnesses: &[PredicateLogicValue],
        expression: &LogicExpression<VirMemoryAccess>,
        budget: &mut LogicBudget,
    ) -> Result<PredicateConstraintFact, PredicateError> {
        Ok(PredicateConstraintFact {
            expression: expression.clone(),
            leaves: self.capture_predicate_logic_leaves(
                definition, resources, scope, parameters, witnesses, expression, budget,
            )?,
        })
    }

    fn same_predicate_constraint(
        &self,
        saved: &PredicateConstraintFact,
        current: &PredicateConstraintFact,
        scope: InstanceScope,
        context: Option<&ExpressionFacts<'_>>,
        budget: &mut LogicBudget,
    ) -> Result<bool, PredicateError> {
        if saved.expression != current.expression || saved.leaves.len() != current.leaves.len() {
            return Ok(false);
        }
        if saved
            .leaves
            .iter()
            .zip(&current.leaves)
            .any(|((a, old), (b, new))| a != b || old.ty != new.ty)
        {
            return Ok(false);
        }
        // Reconcile the complete capture once. A memory address without an
        // immutable origin is still unavailable; matching shapes cannot make
        // it a saved premise.
        let values = saved
            .leaves
            .iter()
            .chain(&current.leaves)
            .map(|(_, value)| value.clone())
            .collect::<Vec<_>>();
        let mut shared = context
            .filter(|context| context.qualified.borrow().is_initialized())
            .map(|context| context.qualified.borrow_mut());
        let mut local = fact_inputs::Facts::new();
        let (prepared, facts) = if let Some(qualified) = shared.as_deref_mut() {
            let context = context.unwrap();
            if !qualified.matches(self, scope, context.saved) {
                return Err(PredicateError::InvalidBinding);
            }
            (qualified.queries(&values, budget)?, &qualified.facts)
        } else {
            (
                self.prepare_logic_fact_values(&values, Some(scope), &mut local, budget)?,
                &local,
            )
        };
        let (saved, current) = prepared.split_at(saved.leaves.len());
        for (old, new) in saved.iter().zip(current) {
            let (Some(old), Some(new)) = (old, new) else {
                return Ok(false);
            };
            let equal = match (&old.value, &new.value) {
                (LogicValue::Word(a), LogicValue::Word(b)) => a.equal(b) == Some(true),
                (LogicValue::Resource(a), LogicValue::Resource(b)) => a == b,
                (LogicValue::ResourceAtom { atom: a }, LogicValue::ResourceAtom { atom: b }) => {
                    a == b
                }
                (a, b) if old.ty == LogicType::Bool => {
                    a.bool_equal(b) == Some(true)
                        || facts
                            .entails(
                                crate::predicate_logic::facts::Comparison::Equal,
                                old,
                                new,
                                budget,
                            )
                            .map_err(map_error)?
                }
                _ => false,
            };
            if !equal {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Import is called only by the contract adapter after establishing the
    /// actual ABI representation. Normal folds cannot manufacture these facts.
    /// Matching a fact checks leaf identity, not merely equal abstract ranges.
    #[expect(
        clippy::too_many_arguments,
        reason = "Keep boundary identities, state, evidence and shared budget explicit at the resource adapter"
    )]
    pub(super) fn capture_predicate_constraints<'a>(
        &'a self,
        definition: &PredicateDefinition,
        resources: &[SealedResource],
        scope: InstanceScope,
        parameters: &[PredicateLogicValue],
        witnesses: &[PredicateLogicValue],
        available: &'a [PredicateConstraintFact],
        imported: bool,
        context: Option<&ExpressionFacts<'a>>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<PredicateConstraintFact>, PredicateError> {
        if definition.logic.constraints.len() > MAX_CONSTRAINTS || available.len() > MAX_CONSTRAINTS
        {
            return Err(PredicateError::Budget);
        }
        let evaluate = |expression: &LogicExpression<VirMemoryAccess>, budget: &mut LogicBudget| {
            expression.evaluate(
                parameters,
                witnesses,
                &mut |r, o, a, t| {
                    self.observe_predicate_logic(definition, resources, scope, false, (r, o, a, t))
                },
                &mut |r, path| resource_value(self, definition, resources, r, path),
                budget,
            )
        };
        if !imported
            && !available.is_empty()
            && let Some(context) = context
        {
            let mut qualified = context.qualified.borrow_mut();
            if !qualified.matches(self, scope, available) {
                return Err(PredicateError::InvalidBinding);
            }
            qualified.queries(&[], budget)?;
        }
        let mut facts = Vec::new();
        let mut pending = Vec::new();
        for expression in &definition.logic.constraints {
            let snapshot = self.predicate_constraint_snapshot(
                definition, resources, scope, parameters, witnesses, expression, budget,
            )?;
            let mut established = false;
            if imported {
                // Only the ABI adapter can import guarantees. Unknown
                // arithmetic is allowed here; known false/malformed is not.
                match evaluate(expression, budget) {
                    Ok(value)
                        if value.ty == LogicType::Bool
                            && value.value != LogicValue::Bool(Some(false)) => {}
                    Err(LogicError::Overflow | LogicError::Unproved) => {}
                    Err(error) => return Err(map_error(error)),
                    _ => return Err(PredicateError::UnprovedRepresentation),
                }
                established = true;
            } else {
                for old in available {
                    budget.charge(old.leaves.len()).map_err(map_error)?;
                    if self.same_predicate_constraint(old, &snapshot, scope, context, budget)? {
                        established = true;
                        break;
                    }
                }
            }
            if !established {
                pending.push(facts.len());
            }
            facts.push(snapshot);
        }
        if !pending.is_empty() {
            // All pending constraints share one qualification of their input
            // sources. None of their proposed truths enters the premise set.
            let queries = pending
                .iter()
                .flat_map(|index| facts[*index].leaves.iter().map(|(_, value)| value.clone()))
                .collect::<Vec<_>>();
            let mut local = fact_inputs::QualifiedFacts::new(self, Some(scope), available);
            let mut shared = context.map(|context| context.qualified.borrow_mut());
            let qualified = shared.as_deref_mut().unwrap_or(&mut local);
            if !qualified.matches(self, scope, available) {
                return Err(PredicateError::InvalidBinding);
            }
            let prepared = qualified.queries(&queries, budget)?;
            let premises = &qualified.facts;
            let mut start = 0;
            let mut batch = Vec::new();
            for index in &pending {
                let snapshot = &facts[*index];
                let end = start + snapshot.leaves.len();
                let leaves = snapshot
                    .leaves
                    .iter()
                    .zip(&prepared[start..end])
                    .map(|((id, _), value)| (*id, value.clone()))
                    .collect::<Vec<_>>();
                batch.push((&snapshot.expression, leaves));
                start = end;
            }
            let batch_refs = batch
                .iter()
                .map(|(expression, leaves)| (*expression, leaves.as_slice()))
                .collect::<Vec<_>>();
            let proved = premises
                .proves_batch(&batch_refs, budget)
                .map_err(map_error)?;
            for (index, proved) in pending.into_iter().zip(proved) {
                if !proved {
                    let value = evaluate(&facts[index].expression, budget).map_err(map_error)?;
                    if value.ty != LogicType::Bool || value.value != LogicValue::Bool(Some(true)) {
                        return Err(PredicateError::UnprovedRepresentation);
                    }
                }
            }
        }
        Ok(facts)
    }
}

#[cfg(test)]
mod tests;
