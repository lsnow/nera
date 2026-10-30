//! Scalar expression shapes without captured intervals or compiler identities.
//! Adapters establish each leaf binding. Instantiation recomputes checked bounds
//! from the supplied values and never reads resources or creates permissions.
use super::affine::LinearWord;
use super::*;
mod input_types;
mod rebase;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ScalarKind {
    Word,
    Bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct WordTemplate<A: Ord> {
    constant: i128,
    terms: BTreeMap<A, i128>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ScalarTemplate<A: Ord> {
    Word(WordTemplate<A>),
    Bool(bool),
    BoolAtom {
        atom: A,
        negated: bool,
    },
    Comparison {
        word_type: WordType,
        comparison: WordComparison,
        left: WordTemplate<A>,
        right: WordTemplate<A>,
        negated: bool,
    },
    Boolean {
        operation: BooleanOperation,
        left: Box<Self>,
        right: Box<Self>,
        negated: bool,
    },
}

impl<A: Ord + Clone> ScalarTemplate<A> {
    /// Read-only mathematical shape for adapters with a smaller term language.
    /// This does not instantiate the expression or assert machine definedness.
    pub(crate) fn word_shape(&self) -> Option<(i128, &BTreeMap<A, i128>)> {
        match self {
            Self::Word(word) => Some((word.constant, &word.terms)),
            _ => None,
        }
    }

    pub(crate) fn capture<B: Ord, R>(
        value: &LogicValue<B, R>,
        map: &mut impl FnMut(&B, ScalarKind, &mut LogicBudget) -> Result<A, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<Self, LogicError> {
        budget.charge(1)?;
        Ok(match value {
            LogicValue::BoolBinary {
                operation,
                left,
                right,
                negated,
            } => {
                value.capture_leaves(budget)?;
                Self::Boolean {
                    operation: *operation,
                    left: Box::new(Self::capture(left, map, budget)?),
                    right: Box::new(Self::capture(right, map, budget)?),
                    negated: *negated,
                }
            }
            LogicValue::Word(word) => Self::Word(WordTemplate::capture(word, map, budget)?),
            LogicValue::Bool(Some(value)) => Self::Bool(*value),
            LogicValue::BoolAtom { atom, negated, .. } => Self::BoolAtom {
                atom: map(atom, ScalarKind::Bool, budget)?,
                negated: *negated,
            },
            LogicValue::BoolComparison {
                word_type,
                comparison,
                left,
                right,
                negated,
            } => Self::Comparison {
                word_type: *word_type,
                comparison: *comparison,
                left: WordTemplate::capture(left, map, budget)?,
                right: WordTemplate::capture(right, map, budget)?,
                negated: *negated,
            },
            _ => return Err(LogicError::Unbound),
        })
    }

    pub(crate) fn inputs(
        &self,
        budget: &mut LogicBudget,
    ) -> Result<BTreeMap<A, ScalarKind>, LogicError> {
        budget.charge(1)?;
        let mut result = BTreeMap::new();
        match self {
            Self::Boolean { left, right, .. } => {
                for (atom, kind) in left
                    .inputs(budget)?
                    .into_iter()
                    .chain(right.inputs(budget)?)
                {
                    if result.insert(atom, kind).is_some_and(|old| old != kind) {
                        return Err(LogicError::TypeMismatch);
                    }
                }
            }
            Self::Bool(_) => {}
            Self::BoolAtom { atom, .. } => {
                result.insert(atom.clone(), ScalarKind::Bool);
            }
            Self::Word(word) => {
                budget.charge(word.terms.len())?;
                result.extend(word.terms.keys().cloned().map(|a| (a, ScalarKind::Word)));
            }
            Self::Comparison { left, right, .. } => {
                budget.charge(left.terms.len() + right.terms.len())?;
                result.extend(
                    left.terms
                        .keys()
                        .chain(right.terms.keys())
                        .cloned()
                        .map(|a| (a, ScalarKind::Word)),
                );
            }
        }
        Ok(result)
    }

    pub(crate) fn instantiate<B: Ord + Clone, R: Clone>(
        &self,
        read: &mut impl FnMut(&A, ScalarKind, &mut LogicBudget) -> Result<LogicValue<B, R>, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<LogicValue<B, R>, LogicError> {
        self.instantiate_with_domain(read, &mut |_, word, _| word.into_word(), budget)
    }

    /// The domain service receives a mathematical expression, never a value
    /// falsely labelled as an already defined u64. It must prove both bounds.
    /// Comparison operands provide their word type; None denotes a whole-word
    /// result whose declared type remains the adapter's responsibility.
    pub(crate) fn instantiate_with_domain<B: Ord + Clone, R: Clone>(
        &self,
        read: &mut impl FnMut(&A, ScalarKind, &mut LogicBudget) -> Result<LogicValue<B, R>, LogicError>,
        domain: &mut impl FnMut(
            Option<WordType>,
            LinearWord<B>,
            &mut LogicBudget,
        ) -> Result<AffineValue<B>, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<LogicValue<B, R>, LogicError> {
        budget.charge(1)?;
        Ok(match self {
            Self::Boolean {
                operation,
                left,
                right,
                negated,
            } => LogicValue::boolean_binary(
                *operation,
                left.instantiate_with_domain(read, domain, budget)?,
                right.instantiate_with_domain(read, domain, budget)?,
                *negated,
                budget,
            )?,
            Self::Word(word) => {
                LogicValue::Word(domain(None, word.instantiate(read, budget)?, budget)?)
            }
            Self::Bool(value) => LogicValue::Bool(Some(*value)),
            Self::BoolAtom { atom, negated } => {
                let value = read(atom, ScalarKind::Bool, budget)?;
                if !matches!(
                    value,
                    LogicValue::Bool(_)
                        | LogicValue::BoolAtom { .. }
                        | LogicValue::BoolComparison { .. }
                        | LogicValue::BoolBinary { .. }
                ) {
                    return Err(LogicError::TypeMismatch);
                }
                if *negated { value.bool_not() } else { value }
            }
            Self::Comparison {
                word_type,
                comparison,
                left,
                right,
                negated,
            } => LogicValue::word_comparison(
                *word_type,
                *comparison,
                domain(Some(*word_type), left.instantiate(read, budget)?, budget)?,
                domain(Some(*word_type), right.instantiate(read, budget)?, budget)?,
                *negated,
            ),
        })
    }
}

impl<A: Ord + Clone> WordTemplate<A> {
    fn capture<B: Ord>(
        word: &AffineValue<B>,
        map: &mut impl FnMut(&B, ScalarKind, &mut LogicBudget) -> Result<A, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<Self, LogicError> {
        budget.charge(1 + word.terms.len())?;
        if word.terms.len() > MAX_LINEAR_TERMS {
            return Err(LogicError::Budget);
        }
        let mut terms = BTreeMap::<A, i128>::new();
        for (atom, coefficient) in &word.terms {
            let atom = map(atom, ScalarKind::Word, budget)?;
            let entry = terms.entry(atom).or_default();
            *entry = entry
                .checked_add(*coefficient)
                .ok_or(LogicError::Overflow)?;
        }
        terms.retain(|_, c| *c != 0);
        Ok(Self {
            constant: word.constant,
            terms,
        })
    }

    fn instantiate<B: Ord + Clone, R: Clone>(
        &self,
        read: &mut impl FnMut(&A, ScalarKind, &mut LogicBudget) -> Result<LogicValue<B, R>, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<LinearWord<B>, LogicError> {
        budget.charge(1 + self.terms.len())?;
        let mut constant = self.constant;
        let (mut lower, mut upper) = (self.constant, self.constant);
        let mut terms = BTreeMap::<B, i128>::new();
        let add_product = |a: i128, b: i128, c: i128| a.checked_add(b.checked_mul(c)?);
        for (atom, coefficient) in &self.terms {
            let LogicValue::Word(value) = read(atom, ScalarKind::Word, budget)? else {
                return Err(LogicError::TypeMismatch);
            };
            budget.charge(value.terms.len())?;
            if value.lower > value.upper {
                return Err(LogicError::InvalidNode);
            }
            let (lo, hi) = if *coefficient >= 0 {
                (value.lower, value.upper)
            } else {
                (value.upper, value.lower)
            };
            lower = add_product(lower, *coefficient, i128::from(lo)).ok_or(LogicError::Overflow)?;
            upper = add_product(upper, *coefficient, i128::from(hi)).ok_or(LogicError::Overflow)?;
            constant =
                add_product(constant, *coefficient, value.constant).ok_or(LogicError::Overflow)?;
            for (atom, factor) in value.terms {
                let entry = terms.entry(atom).or_default();
                *entry = add_product(*entry, *coefficient, factor).ok_or(LogicError::Overflow)?;
            }
            terms.retain(|_, c| *c != 0);
            if terms.len() > MAX_LINEAR_TERMS {
                return Err(LogicError::Budget);
            }
        }
        Ok(LinearWord {
            lower,
            upper,
            constant,
            terms,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Value = LogicValue<u32, ()>;

    #[test]
    fn mathematical_shape_does_not_claim_undefined_instantiation_is_safe() {
        let input = AffineValue::identified(1, 0, 1).unwrap();
        let plan = capture(&Value::Word(input.add(&AffineValue::exact(1)).unwrap()));
        assert_eq!(plan.word_shape(), Some((1, &BTreeMap::from([(1, 1)]))));
        let result = plan.instantiate(
            &mut |_, _, _| {
                Ok(Value::Word(
                    AffineValue::identified(9, 0, u64::MAX).unwrap(),
                ))
            },
            &mut LogicBudget::default(),
        );
        assert_eq!(result, Err(LogicError::Overflow));
        assert_eq!(ScalarTemplate::<u32>::Bool(true).word_shape(), None);
    }

    #[test]
    fn singleton_observations_keep_input_shapes_but_literals_stay_constant() {
        let observed = AffineValue::identified(1, 0, 0).unwrap();
        let same_number = AffineValue::identified(2, 0, 0).unwrap();
        assert_eq!(observed.equal(&same_number), Some(true));
        assert_ne!(observed.terms, same_number.terms);
        let plan = capture(&Value::Word(observed.add(&AffineValue::exact(1)).unwrap()));
        assert_eq!(
            plan.inputs(&mut LogicBudget::default()).unwrap(),
            BTreeMap::from([(1, ScalarKind::Word)])
        );
        let result = plan
            .instantiate(
                &mut |_, _, _| Ok(Value::Word(AffineValue::identified(9, 0, 7).unwrap())),
                &mut LogicBudget::default(),
            )
            .unwrap();
        let Value::Word(result) = result else {
            panic!()
        };
        assert_eq!((result.lower, result.upper), (1, 8));
        assert_eq!(result.terms, BTreeMap::from([(9, 1)]));
        let literal = capture(&Value::Word(AffineValue::exact(1)));
        assert!(
            literal
                .inputs(&mut LogicBudget::default())
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            AffineValue::identified(1, 2, 1),
            Err(LogicError::InvalidNode)
        );
        assert_eq!(
            AffineValue::identified(1, u64::MAX, u64::MAX)
                .unwrap()
                .add(&AffineValue::exact(1)),
            Err(LogicError::Overflow)
        );
    }

    fn capture(value: &Value) -> ScalarTemplate<u32> {
        ScalarTemplate::capture(
            value,
            &mut |atom, _, _| Ok(*atom),
            &mut LogicBudget::default(),
        )
        .unwrap()
    }

    #[test]
    fn re_evaluation_discards_captured_bounds_and_retains_affine_shape() {
        let old = AffineValue::variable(1, 1, 3)
            .unwrap()
            .scale(2)
            .unwrap()
            .add(&AffineValue::exact(1))
            .unwrap();
        let template = capture(&Value::Word(old));
        let result: Value = template
            .instantiate(
                &mut |slot, kind, _| {
                    assert_eq!((*slot, kind), (1, ScalarKind::Word));
                    Ok(Value::Word(AffineValue::variable(99, 5, 9).unwrap()))
                },
                &mut LogicBudget::default(),
            )
            .unwrap();
        assert_eq!(
            result,
            Value::Word(AffineValue {
                lower: 11,
                upper: 19,
                constant: 1,
                terms: BTreeMap::from([(99, 2)]),
            })
        );
        let wider = AffineValue::variable(1, 0, 8)
            .unwrap()
            .scale(2)
            .unwrap()
            .add(&AffineValue::exact(1))
            .unwrap();
        assert_eq!(template, capture(&Value::Word(wider)));
        let subtraction = capture(&Value::Word(
            AffineValue::exact(10)
                .sub(&AffineValue::variable(1, 1, 3).unwrap())
                .unwrap(),
        ));
        assert_eq!(
            subtraction
                .instantiate(
                    &mut |_, _, _| Ok(Value::Word(AffineValue::variable(99, 0, 7).unwrap())),
                    &mut LogicBudget::default()
                )
                .unwrap(),
            Value::Word(AffineValue {
                lower: 3,
                upper: 10,
                constant: 10,
                terms: BTreeMap::from([(99, -1)])
            })
        );
    }

    #[test]
    fn boolean_polarity_and_comparisons_use_new_inputs() {
        let negated = capture(&Value::BoolAtom {
            atom: 1,
            negated: true,
            known: None,
        });
        assert_eq!(
            negated
                .instantiate(
                    &mut |_, kind, _| {
                        assert_eq!(kind, ScalarKind::Bool);
                        Ok(Value::Bool(Some(true)))
                    },
                    &mut LogicBudget::default()
                )
                .unwrap(),
            Value::Bool(Some(false))
        );
        let comparison = capture(&Value::BoolComparison {
            word_type: WordType::Usize,
            comparison: WordComparison::LessEqual,
            left: AffineValue::variable(1, 0, 8).unwrap(),
            right: AffineValue::variable(2, 0, 8).unwrap(),
            negated: false,
        });
        assert_eq!(
            comparison
                .instantiate(
                    &mut |id, _, _| Ok(Value::Word(AffineValue::exact(u64::from(*id)))),
                    &mut LogicBudget::default()
                )
                .unwrap(),
            Value::Bool(Some(true))
        );
    }

    #[test]
    fn domain_type_and_budget_failures_do_not_reuse_the_entry_range() {
        let template = capture(&Value::Word(
            AffineValue::variable(1, 0, 1)
                .unwrap()
                .add(&AffineValue::exact(1))
                .unwrap(),
        ));
        assert_eq!(
            template.instantiate(
                &mut |_, _, _| Ok(Value::Word(AffineValue::variable(99, 0, u64::MAX).unwrap())),
                &mut LogicBudget::default()
            ),
            Err(LogicError::Overflow)
        );
        assert_eq!(
            template.instantiate(
                &mut |_, _, _| Ok(Value::Bool(Some(true))),
                &mut LogicBudget::default()
            ),
            Err(LogicError::TypeMismatch)
        );
        let negative = capture(&Value::Word(
            AffineValue::exact(1)
                .sub(&AffineValue::variable(1, 0, 1).unwrap())
                .unwrap(),
        ));
        assert_eq!(
            negative.instantiate(
                &mut |_, _, _| Ok(Value::Word(AffineValue::variable(99, 2, 3).unwrap())),
                &mut LogicBudget::default()
            ),
            Err(LogicError::Overflow)
        );
        let mut budget = LogicBudget::default();
        budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
        assert_eq!(
            template.instantiate(
                &mut |_, _, _| Ok(Value::Word(AffineValue::exact(0))),
                &mut budget
            ),
            Err(LogicError::Budget)
        );
        assert_eq!(
            ScalarTemplate::<u32>::capture(
                &Value::Resource(()),
                &mut |a, _, _| Ok(*a),
                &mut LogicBudget::default()
            ),
            Err(LogicError::Unbound)
        );
    }
}

#[cfg(test)]
mod relational_tests {
    use super::*;
    use crate::predicate_logic::facts::EstablishedFacts;
    type Value = LogicValue<u32, ()>;
    fn word(id: u32, lo: u64, hi: u64) -> TypedLogicValue<(), u32, ()> {
        TypedLogicValue {
            ty: LogicType::Usize,
            value: Value::Word(AffineValue::variable(id, lo, hi).unwrap()),
        }
    }

    #[test]
    fn difference_domain_uses_current_relations_not_entry_bounds_or_old_names() {
        let entry = Value::Word(
            AffineValue::variable(1, 5, 9)
                .unwrap()
                .sub(&AffineValue::variable(2, 0, 4).unwrap())
                .unwrap(),
        );
        let template =
            ScalarTemplate::capture(&entry, &mut |id, _, _| Ok(*id), &mut LogicBudget::default())
                .unwrap();
        for related in [false, true] {
            let mut facts = EstablishedFacts::new();
            // The wrong namespace must not support the newly substituted leaves.
            let (high, low) = if related { (11, 12) } else { (1, 2) };
            facts
                .extend_difference(
                    &word(low, 0, 9),
                    &word(high, 0, 9),
                    0,
                    &mut LogicBudget::default(),
                )
                .unwrap();
            let value = template.instantiate_with_domain(
                &mut |id, _, _| Ok(word(*id + 10, 0, 9).value),
                &mut |_, w, budget| facts.check_word_domain(LogicType::Usize, w, budget),
                &mut LogicBudget::default(),
            );
            if related {
                assert_eq!(
                    value,
                    Ok(Value::Word(AffineValue {
                        constant: 0,
                        terms: BTreeMap::from([(11, 1), (12, -1)]),
                        lower: 0,
                        upper: 9
                    }))
                );
            } else {
                assert!(value.is_err());
            }
        }
    }

    #[test]
    fn upper_domain_type_and_budget_are_checked_independently_of_lower_bound() {
        let entry = Value::Word(
            AffineValue::variable(1, 0, 3)
                .unwrap()
                .add(&AffineValue::exact(1))
                .unwrap(),
        );
        let template =
            ScalarTemplate::capture(&entry, &mut |id, _, _| Ok(*id), &mut LogicBudget::default())
                .unwrap();
        for ty in [LogicType::Usize, LogicType::U64] {
            let mut facts = EstablishedFacts::new();
            let mut high = word(11, 0, u64::MAX);
            high.ty = ty;
            let zero = TypedLogicValue {
                ty,
                value: Value::Word(AffineValue::exact(0)),
            };
            facts
                .extend_difference(
                    &high,
                    &zero,
                    i128::from(u64::MAX - 1),
                    &mut LogicBudget::default(),
                )
                .unwrap();
            let result = template.instantiate_with_domain(
                &mut |_, _, _| Ok(word(11, 0, u64::MAX).value),
                &mut |_, w, budget| facts.check_word_domain(LogicType::Usize, w, budget),
                &mut LogicBudget::default(),
            );
            assert_eq!(result.is_ok(), ty == LogicType::Usize);
            let mut budget = LogicBudget::default();
            budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
            assert_eq!(
                template.instantiate_with_domain(
                    &mut |_, _, _| Ok(word(11, 0, 3).value),
                    &mut |_, w, budget| facts.check_word_domain(LogicType::Usize, w, budget),
                    &mut budget,
                ),
                Err(LogicError::Budget)
            );
        }
    }
}
