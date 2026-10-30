//! Bind inductive public parameters to actual header scalar slots. This is an
//! induction adapter, not a proof that an entry capture equals a later value.
//! Each entry and backedge must establish the package at the selected slots.
use super::*;
use crate::predicate_logic::scalar_template::{ScalarKind, ScalarTemplate};
use crate::predicate_logic::{InstanceScope, LogicBudget, LogicError, LogicType};

/// The CFG proves which slots survive an iteration. Retained leaves additionally
/// pin the immutable capture: reusing a slot or its bounds cannot replace it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum LoopParameterLeaf {
    Changing(VirValueId),
    Retained {
        slot: VirValueId,
        capture: logic::ScalarCapture,
    },
}

impl LoopParameterLeaf {
    fn slot(self) -> VirValueId {
        match self {
            Self::Changing(slot) | Self::Retained { slot, .. } => slot,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LoopParameterExpression {
    ty: LogicType<VirMemoryAccess>,
    expression: ScalarTemplate<LoopParameterLeaf>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::verifier) struct LoopPredicateParameters {
    bindings: BTreeMap<PredicateHolder, BTreeMap<usize, LoopParameterExpression>>,
}

impl LoopPredicateParameters {
    pub(super) fn expression(
        &self,
        holder: PredicateHolder,
        position: usize,
    ) -> Option<&LoopParameterExpression> {
        self.bindings.get(&holder)?.get(&position)
    }
}

impl ResourceState {
    /// Rebase complete affine sources onto live changing slots first. Residual
    /// expressions can use complete retained sources before atomic captures.
    /// Equivalent retained copies select one deterministic representative;
    /// reading reconciles all aliases and rechecks the complete origin.
    /// The caller supplies the CFG preservation proof as disjoint slot sets;
    /// numeric bounds, foreign captures and ambiguous changing fanout are insufficient.
    pub(in crate::verifier) fn loop_predicate_parameters(
        &self,
        changing: &BTreeSet<VirValueId>,
        retained: &BTreeSet<VirValueId>,
        repacked: &BTreeSet<PredicateHolder>,
    ) -> Result<LoopPredicateParameters, PredicateError> {
        if !changing.is_disjoint(retained) {
            return Err(PredicateError::InvalidBinding);
        }
        if repacked.len() > MAX_PREDICATE_INSTANCES
            || self.predicates.len() > MAX_PREDICATE_INSTANCES
        {
            return Err(PredicateError::Budget);
        }
        let mut result = LoopPredicateParameters::default();
        let mut budget = LogicBudget::default();
        for holder in repacked {
            let instance = self
                .predicates
                .get(holder)
                .ok_or(PredicateError::MissingHolder)?;
            if !self.sealed_loop_predicate_valid(instance) {
                return Err(PredicateError::UnprovedRepresentation);
            }
            if instance.logical_local_aliases.len() > MAX_PREDICATE_LOCAL_ALIASES {
                return Err(PredicateError::Budget);
            }
            let sources = self
                .predicate_word_sources(instance, changing, &mut budget)?
                .into_iter()
                .map(|(slot, _, word)| (LoopParameterLeaf::Changing(slot), word))
                .collect::<Vec<_>>();
            let fixed_sources = self
                .predicate_retained_word_sources(instance, retained, &mut budget)?
                .into_iter()
                .map(|(slot, capture, word)| (LoopParameterLeaf::Retained { slot, capture }, word))
                .collect::<Vec<_>>();
            for (position, value) in instance.logical_parameters.iter().enumerate() {
                budget.charge(1).map_err(logic::map_error)?;
                let expression = ScalarTemplate::capture_rebased(
                    &value.value,
                    &sources,
                    &fixed_sources,
                    &mut |atom, kind, budget| {
                        let capture = logic::ScalarCapture::from_atom(atom, kind)
                            .ok_or(LogicError::Unbound)?;
                        // Prefer a unique changing slot over retained copies of
                        // the entry value. This chooses an induction hypothesis,
                        // not an equality: every backedge must establish it.
                        for (candidates, dynamic) in [(changing, true), (retained, false)] {
                            let mut slot = None;
                            for id in candidates {
                                budget.charge(1)?;
                                if self.predicate_capture_matches(instance, capture, *id, kind) {
                                    if dynamic && slot.is_some() {
                                        return Err(LogicError::Unbound);
                                    }
                                    slot.get_or_insert(*id);
                                }
                            }
                            if let Some(slot) = slot {
                                return Ok(if dynamic {
                                    LoopParameterLeaf::Changing(slot)
                                } else {
                                    LoopParameterLeaf::Retained { slot, capture }
                                });
                            }
                        }
                        Err(LogicError::Unbound)
                    },
                    &mut budget,
                );
                let expression = match expression {
                    Ok(expression) => expression,
                    Err(LogicError::Unbound) => continue,
                    Err(error) => return Err(logic::map_error(error)),
                };
                // Entirely fixed expressions keep the original public value.
                if expression
                    .typed_inputs(value.ty, &mut budget)
                    .map_err(logic::map_error)?
                    .keys()
                    .any(|leaf| matches!(leaf, LoopParameterLeaf::Changing(_)))
                {
                    result.bindings.entry(*holder).or_default().insert(
                        position,
                        LoopParameterExpression {
                            ty: value.ty,
                            expression,
                        },
                    );
                }
            }
        }
        Ok(result)
    }

    pub(super) fn loop_parameter_actual(
        &self,
        instance: &PredicateInstance,
        binding: &LoopParameterExpression,
        budget: &mut LogicBudget,
    ) -> Result<logic::PredicateLogicValue, PredicateError> {
        let scope = instance.logic_scope.ok_or(PredicateError::InvalidBinding)?;
        let mut inputs = BTreeMap::new();
        for (leaf, ty) in binding
            .expression
            .typed_inputs(binding.ty, budget)
            .map_err(logic::map_error)?
        {
            let value = match leaf {
                LoopParameterLeaf::Retained { slot, capture } => {
                    self.read_predicate_capture(instance, capture, slot, ty, budget)?
                }
                LoopParameterLeaf::Changing(slot) => {
                    self.predicate_scalar_input(scope, ty, slot, &instance.logical_local_aliases)?
                }
            };
            if let Some(previous) = inputs.insert(leaf.slot(), value)
                && previous.ty != ty
            {
                return Err(PredicateError::InvalidBinding);
            }
        }
        // Only established current scalar relations support this domain query.
        // The package being abstracted must not justify its own reconstruction.
        let facts = self.predicate_scalar_relations(&inputs, budget)?;
        let value = binding
            .expression
            .instantiate_with_domain(
                &mut |leaf, _, _| {
                    inputs
                        .get(&leaf.slot())
                        .map(|v| v.value.clone())
                        .ok_or(LogicError::Unbound)
                },
                &mut |word_type, word, budget| {
                    facts.check_word_domain(
                        word_type.map(|ty| ty.logic_type()).unwrap_or(binding.ty),
                        word,
                        budget,
                    )
                },
                budget,
            )
            .map_err(logic::map_error)?;
        Ok(crate::predicate_logic::TypedLogicValue {
            ty: binding.ty,
            value,
        })
    }

    /// Called only after admitting the original entry and establishing the
    /// real resource frame. The new public values are provisional induction
    /// premises; the same immutable plan is mandatory on every backedge.
    pub(super) fn bind_loop_predicate_parameters(
        &self,
        holder: PredicateHolder,
        instance: &mut PredicateInstance,
        plan: &LoopPredicateParameters,
        scope: InstanceScope,
        budget: &mut LogicBudget,
    ) -> Result<(), PredicateError> {
        let Some(bindings) = plan.bindings.get(&holder) else {
            return Ok(());
        };
        // Bind every changing leaf before evaluating any parameter. Retained
        // leaves keep their old capture, including when a fixed public parameter
        // also uses it. Never repair a missing retained alias here.
        for binding in bindings.values() {
            for (leaf, ty) in binding
                .expression
                .typed_inputs(binding.ty, budget)
                .map_err(logic::map_error)?
            {
                let kind = match ty {
                    LogicType::Bool => ScalarKind::Bool,
                    LogicType::U64 | LogicType::Usize => ScalarKind::Word,
                    _ => return Err(PredicateError::InvalidBinding),
                };
                let slot = leaf.slot();
                if !scalar_type_matches(ty, self.value(slot)) {
                    return Err(PredicateError::InvalidBinding);
                }
                match leaf {
                    LoopParameterLeaf::Changing(_) => {
                        instance
                            .logical_local_aliases
                            .insert(slot, logic::LocalSnapshot { scope, value: slot });
                    }
                    LoopParameterLeaf::Retained { capture, .. } => {
                        if !self.predicate_capture_matches(instance, capture, slot, kind) {
                            return Err(PredicateError::InvalidBinding);
                        }
                    }
                }
            }
        }
        for (position, binding) in bindings {
            budget.charge(1).map_err(logic::map_error)?;
            let ty = instance
                .logical_parameters
                .get(*position)
                .ok_or(PredicateError::InvalidBinding)?
                .ty;
            if ty != binding.ty {
                return Err(PredicateError::InvalidBinding);
            }
            let value = self.loop_parameter_actual(instance, binding, budget)?;
            instance.logical_parameters[*position] = value;
        }
        if instance.logical_local_aliases.len() > MAX_PREDICATE_LOCAL_ALIASES {
            return Err(PredicateError::Budget);
        }
        Ok(())
    }
}

fn scalar_type_matches(ty: LogicType<VirMemoryAccess>, value: Option<&AbstractValue>) -> bool {
    matches!(
        (ty, value),
        (
            LogicType::U64 | LogicType::Usize,
            Some(AbstractValue::U64(_))
        ) | (LogicType::Bool, Some(AbstractValue::Bool(_)))
    )
}
