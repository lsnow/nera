//! Qualify immutable snapshots and project current observations without erasing
//! capture identities. Runtime sources are inspected only in this adapter;
//! the pure service receives explicit typed scalar facts, never a heap handle.
use super::*;
use crate::predicate_logic::facts::EstablishedFacts;
use crate::verifier::relation::state::RelationOperand;
mod context;
pub(super) use context::QualifiedFacts;

pub(super) type Facts = EstablishedFacts<VirMemoryAccess, ObservationAtom, ResourceWitness>;

impl ResourceState {
    /// Resolve only local immutable origins using surviving, bounded SSA facts.
    /// Captured foreign symbols and equal-looking unknowns supply no evidence.
    pub(super) fn refine_predicate_boolean(
        &self,
        mut value: PredicateLogicValue,
    ) -> PredicateLogicValue {
        if let LogicValue::BoolBinary {
            operation,
            left,
            right,
            negated,
        } = &value.value
        {
            if value
                .value
                .capture_leaves(&mut LogicBudget::default())
                .is_err()
            {
                return value;
            }
            let left = self.refine_predicate_boolean(TypedLogicValue {
                ty: value.ty,
                value: *left.clone(),
            });
            let right = self.refine_predicate_boolean(TypedLogicValue {
                ty: value.ty,
                value: *right.clone(),
            });
            value.value = LogicValue::BoolBinary {
                operation: *operation,
                left: Box::new(left.value),
                right: Box::new(right.value),
                negated: *negated,
            };
            if let Some(known) = value.value.known_boolean() {
                value.value = LogicValue::Bool(Some(known));
            }
            return value;
        }
        if let LogicValue::BoolComparison {
            comparison,
            left,
            right,
            negated,
            ..
        } = &value.value
        {
            if let (Some((left, left_aliases)), Some((right, right_aliases))) = (
                self.refine_predicate_word(left),
                self.refine_predicate_word(right),
            ) {
                let known = match comparison {
                    WordComparison::Equal => left.equal(&right),
                    WordComparison::LessEqual => left.less_equal(&right),
                }
                .or_else(|| {
                    self.predicate_comparison_relation(
                        *comparison,
                        &left,
                        &right,
                        &left_aliases,
                        &right_aliases,
                    )
                });
                if let Some(known) = known {
                    value.value = LogicValue::Bool(Some(known ^ *negated));
                }
            }
            return value;
        }
        let LogicValue::BoolAtom {
            atom:
                ObservationAtom::HistoricalBool {
                    origin,
                    local: true,
                    ..
                },
            negated,
            ..
        } = &value.value
        else {
            return value;
        };
        let mut known = None;
        for (id, candidate) in &self.bool_origins {
            if candidate != origin {
                continue;
            }
            let fact = match self.value(*id) {
                Some(AbstractValue::Bool(AbstractBool::True)) => true,
                Some(AbstractValue::Bool(AbstractBool::False)) => false,
                _ => continue,
            };
            if known.is_some_and(|previous| previous != fact) {
                return value;
            }
            known = Some(fact);
        }
        if let Some(fact) = known {
            value.value = LogicValue::Bool(Some(fact != *negated));
        }
        value
    }

    /// Read current bounds only for the exact immutable affine origin saved in
    /// this local snapshot. This never uses equal intervals as alias evidence.
    pub(super) fn refine_predicate_word(
        &self,
        saved: &AffineValue<ObservationAtom>,
    ) -> Option<(AffineValue<ObservationAtom>, BTreeSet<VirValueId>)> {
        if saved.terms.is_empty() && saved.lower == saved.upper {
            // Numeric constants need no origin identity. Restrict the search
            // to the bounded relation table, including a non-endpoint `x != c`
            // that cannot be represented by narrowing x's interval.
            let aliases = self
                .relations
                .bounds()
                .flat_map(|bound| [bound.left, bound.right].into_iter().flatten())
                .chain(
                    self.relations
                        .disequalities()
                        .iter()
                        .flat_map(|(a, b)| [a.value(), b.value()])
                        .flatten(),
                )
                .filter(|id| {
                    matches!(self.value(*id), Some(AbstractValue::U64(value))
                    if value.exact_value() == Some(saved.lower))
                })
                .collect();
            return Some((saved.clone(), aliases));
        }
        let Some(ObservationAtom::Historical {
            scope, local: true, ..
        }) = saved.terms.keys().next()
        else {
            return Some((saved.clone(), BTreeSet::new()));
        };
        if !saved.terms.keys().all(|atom| {
            matches!(atom,
            ObservationAtom::Historical { scope: other, local: true, .. } if other == scope)
        }) {
            return Some((saved.clone(), BTreeSet::new()));
        }
        let mut refined = saved.clone();
        let mut aliases = BTreeSet::new();
        // The SSA source table is bounded; each candidate has at most two
        // immutable historical roots. Do not guess relations to foreign frames.
        for (id, origin) in &self.word_origins {
            let Some(AbstractValue::U64(interval)) = self.value(*id) else {
                continue;
            };
            if !observations::matches_word_origin(*scope, *origin, saved) {
                continue;
            }
            aliases.insert(*id);
            refined.lower = refined.lower.max(interval.lower());
            refined.upper = refined.upper.min(interval.upper());
            if refined.lower > refined.upper {
                // Conflicting source facts must not be cherry-picked to prove
                // either truth value of the comparison.
                return None;
            }
        }
        Some((refined, aliases))
    }

    /// Consult only already established difference facts. No solver, new
    /// premise, or guessed equality is installed by matching a predicate.
    fn predicate_comparison_relation(
        &self,
        comparison: WordComparison,
        left_word: &AffineValue<ObservationAtom>,
        right_word: &AffineValue<ObservationAtom>,
        left: &BTreeSet<VirValueId>,
        right: &BTreeSet<VirValueId>,
    ) -> Option<bool> {
        let matches = |endpoint: RelationOperand,
                       aliases: &BTreeSet<VirValueId>,
                       word: &AffineValue<ObservationAtom>| match endpoint {
            RelationOperand::Value(id) => aliases.contains(&id),
            RelationOperand::Constant(value) => word.lower == value && word.upper == value,
        };
        let identity = !left.is_disjoint(right);
        let mut forward = identity.then_some(0);
        let mut backward = forward;
        for bound in self.relations.bounds() {
            let (Some(a), Some(b)) = (bound.left, bound.right) else {
                continue;
            };
            if left.contains(&a) && right.contains(&b) {
                forward = Some(forward.map_or(bound.bound, |old: i128| old.min(bound.bound)));
            }
            if right.contains(&a) && left.contains(&b) {
                backward = Some(backward.map_or(bound.bound, |old: i128| old.min(bound.bound)));
            }
        }
        let (proven, refuted) = match comparison {
            WordComparison::LessEqual => (
                forward.is_some_and(|n| n <= 0),
                backward.is_some_and(|n| n < 0),
            ),
            WordComparison::Equal => (
                forward.is_some_and(|n| n <= 0) && backward.is_some_and(|n| n <= 0),
                forward.is_some_and(|n| n < 0)
                    || backward.is_some_and(|n| n < 0)
                    || self.relations.disequalities().iter().any(|(a, b)| {
                        (matches(*a, left, left_word) && matches(*b, right, right_word))
                            || (matches(*b, left, left_word) && matches(*a, right, right_word))
                    }),
            ),
        };
        match (proven, refuted) {
            (true, false) => Some(true),
            (false, true) => Some(false),
            _ => None,
        }
    }

    fn fact_input_word(
        &self,
        word: &AffineValue<ObservationAtom>,
        budget: &mut LogicBudget,
    ) -> Result<(AffineValue<ObservationAtom>, BTreeSet<VirValueId>), PredicateError> {
        // Account for source reconciliation and the bounded constant-alias
        // lookup before consulting the runtime adapter's tables.
        let cost = if word.terms.is_empty() {
            2 * (self.relations.bounds().count() + self.relations.disequalities().len())
        } else {
            self.word_origins.len()
        };
        budget.charge(cost).map_err(map_error)?;
        self.refine_predicate_word(word)
            .ok_or(PredicateError::UnprovedRepresentation)
    }

    /// Qualify the complete query context before publishing any observation.
    /// Numeric endpoints can occur in different leaves or saved clauses.
    pub(super) fn prepare_logic_fact_values(
        &self,
        values: &[PredicateLogicValue],
        scope: Option<InstanceScope>,
        facts: &mut Facts,
        budget: &mut LogicBudget,
    ) -> Result<Vec<Option<PredicateLogicValue>>, PredicateError> {
        budget.charge(values.len()).map_err(map_error)?;
        let mut observations = Vec::new();
        let mut prepared = Vec::with_capacity(values.len());
        for value in values {
            prepared.push(self.qualify_logic_fact_value(
                value.clone(),
                scope,
                &mut observations,
                budget,
            )?);
        }
        let numeric = self.predicate_numeric_inputs(prepared.iter().flatten(), budget)?;
        observations.extend(numeric.booleans);
        facts
            .extend_observations(&observations, &numeric.differences, budget)
            .map_err(map_error)?;
        Ok(prepared)
    }

    #[cfg(test)]
    pub(super) fn prepare_logic_fact_value(
        &self,
        value: PredicateLogicValue,
        scope: Option<InstanceScope>,
        facts: &mut Facts,
        budget: &mut LogicBudget,
    ) -> Result<Option<PredicateLogicValue>, PredicateError> {
        Ok(self
            .prepare_logic_fact_values(&[value], scope, facts, budget)?
            .remove(0))
    }

    fn qualify_logic_fact_value(
        &self,
        mut value: PredicateLogicValue,
        scope: Option<InstanceScope>,
        observations: &mut Vec<(PredicateLogicValue, bool)>,
        budget: &mut LogicBudget,
    ) -> Result<Option<PredicateLogicValue>, PredicateError> {
        if !assumptions::reusable_leaf(&value, budget)? {
            return Ok(None);
        }
        if let Some(scope) = scope {
            rebind_local_origins(&mut value, scope, budget).map_err(map_error)?;
        }
        if value.ty == LogicType::Bool {
            value.value = value
                .value
                .canonical_boolean_capture(budget)
                .map_err(map_error)?;
        }
        // Traverse every child before publishing observations. A true outer OR
        // cannot hide an inconsistent nested source or spend a fresh budget.
        for leaf in value.value.capture_leaves_mut(budget).map_err(map_error)? {
            budget.charge(1).map_err(map_error)?;
            let truth = match leaf {
                LogicValue::Word(word) => {
                    let (refined, _) = self.fact_input_word(word, budget)?;
                    *word = refined;
                    None
                }
                LogicValue::BoolComparison {
                    comparison,
                    left,
                    right,
                    negated,
                    ..
                } => {
                    let (a, a_sources) = self.fact_input_word(left, budget)?;
                    let (b, b_sources) = self.fact_input_word(right, budget)?;
                    *left = a;
                    *right = b;
                    let mut known = match comparison {
                        WordComparison::Equal => left.equal(right),
                        WordComparison::LessEqual => left.less_equal(right),
                    };
                    if known.is_none() {
                        budget
                            .charge(
                                self.relations.bounds().count()
                                    + self.relations.disequalities().len(),
                            )
                            .map_err(map_error)?;
                        known = self.predicate_comparison_relation(
                            *comparison,
                            left,
                            right,
                            &a_sources,
                            &b_sources,
                        );
                    }
                    known.map(|known| known ^ *negated)
                }
                LogicValue::BoolAtom {
                    atom:
                        ObservationAtom::HistoricalBool {
                            origin,
                            local: true,
                            ..
                        },
                    negated,
                    ..
                } => {
                    let mut known = None;
                    for (id, candidate) in &self.bool_origins {
                        budget.charge(1).map_err(map_error)?;
                        if candidate != origin {
                            continue;
                        }
                        let current = match self.value(*id) {
                            Some(AbstractValue::Bool(AbstractBool::True)) => true,
                            Some(AbstractValue::Bool(AbstractBool::False)) => false,
                            Some(AbstractValue::Bool(AbstractBool::Unknown)) => continue,
                            _ => return Err(PredicateError::InvalidBinding),
                        };
                        if known.is_some_and(|old| old != current) {
                            return Err(PredicateError::UnprovedRepresentation);
                        }
                        known = Some(current);
                    }
                    known.map(|known| known ^ *negated)
                }
                _ => None,
            };
            if let Some(truth) = truth
                && leaf.known_boolean() != Some(truth)
            {
                observations.push((
                    TypedLogicValue {
                        ty: LogicType::Bool,
                        value: leaf.clone(),
                    },
                    truth,
                ));
            }
        }
        Ok(Some(value))
    }
}

#[cfg(test)]
mod tests;
