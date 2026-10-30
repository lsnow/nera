//! Exact integral substitution of supplied affine sources. This is algebra,
//! not provenance discovery or machine-domain proof; adapters admit sources and
//! instantiation checks the resulting domain against current leaf values.
use super::*;
mod basis;
#[cfg(test)]
mod capture_tests;

impl<A: Ord + Clone> ScalarTemplate<A> {
    /// Change coordinates of an immutable capture, preserving its established
    /// bounds and Boolean shape. Each supplied source denotes exactly its
    /// polynomial; this is not instantiation at new runtime inputs. Adapters
    /// must establish that equality and prevent output-name collisions.
    /// A complete source match takes priority so dependent live coordinates
    /// retain their own names; unmatched words still need an independent basis.
    pub(crate) fn rebase_capture<B: Ord + Clone, R>(
        value: &LogicValue<B, R>,
        sources: &[(A, AffineValue<B>)],
        map: &mut impl FnMut(&B, ScalarKind, &mut LogicBudget) -> Result<A, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<LogicValue<A, R>, LogicError> {
        if let LogicValue::BoolBinary {
            operation,
            left,
            right,
            negated,
        } = value
        {
            value.capture_leaves(budget)?;
            return LogicValue::boolean_binary(
                *operation,
                Self::rebase_capture(left, sources, map, budget)?,
                Self::rebase_capture(right, sources, map, budget)?,
                *negated,
                budget,
            );
        }
        let template = Self::capture_with_policy(
            value,
            sources,
            &[],
            map,
            budget,
            basis::SourcePolicy::ExactCapture,
        )?;
        let word = |template: WordTemplate<A>, original: &AffineValue<B>| {
            if original.lower > original.upper {
                return Err(LogicError::InvalidNode);
            }
            Ok(AffineValue {
                constant: template.constant,
                terms: template.terms,
                lower: original.lower,
                upper: original.upper,
            })
        };
        Ok(match (template, value) {
            (Self::Word(template), LogicValue::Word(original)) => {
                LogicValue::Word(word(template, original)?)
            }
            (Self::Bool(value), _) => LogicValue::Bool(Some(value)),
            (Self::BoolAtom { atom, negated }, LogicValue::BoolAtom { known, .. }) => {
                LogicValue::BoolAtom {
                    atom,
                    negated,
                    known: *known,
                }
            }
            (
                Self::Comparison {
                    word_type,
                    comparison,
                    left,
                    right,
                    negated,
                },
                LogicValue::BoolComparison {
                    left: old_left,
                    right: old_right,
                    ..
                },
            ) => LogicValue::BoolComparison {
                word_type,
                comparison,
                left: word(left, old_left)?,
                right: word(right, old_right)?,
                negated,
            },
            _ => return Err(LogicError::InvalidNode),
        })
    }

    /// Required independent sources are substituted first. Retained sources
    /// are alternative descriptions of immutable values, so dependent copies
    /// may be omitted. Every selected input still needs an actual reader.
    pub(crate) fn capture_rebased<B: Ord + Clone, R>(
        value: &LogicValue<B, R>,
        sources: &[(A, AffineValue<B>)],
        retained: &[(A, AffineValue<B>)],
        map: &mut impl FnMut(&B, ScalarKind, &mut LogicBudget) -> Result<A, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<Self, LogicError> {
        Self::capture_with_policy(
            value,
            sources,
            retained,
            map,
            budget,
            basis::SourcePolicy::Independent,
        )
    }

    fn capture_with_policy<B: Ord + Clone, R>(
        value: &LogicValue<B, R>,
        sources: &[(A, AffineValue<B>)],
        retained: &[(A, AffineValue<B>)],
        map: &mut impl FnMut(&B, ScalarKind, &mut LogicBudget) -> Result<A, LogicError>,
        budget: &mut LogicBudget,
        policy: basis::SourcePolicy,
    ) -> Result<Self, LogicError> {
        budget.charge(1 + sources.len() + retained.len())?;
        let mut keys = BTreeSet::new();
        for (key, word) in sources.iter().chain(retained) {
            budget.charge(1 + word.terms.len())?;
            if word.terms.len() > MAX_LINEAR_TERMS {
                return Err(LogicError::Budget);
            }
            if !keys.insert(key) || word.lower > word.upper || word.terms.values().any(|c| *c == 0)
            {
                return Err(LogicError::InvalidNode);
            }
        }
        match value {
            LogicValue::BoolBinary {
                operation,
                left,
                right,
                negated,
            } => {
                value.capture_leaves(budget)?;
                Ok(Self::Boolean {
                    operation: *operation,
                    left: Box::new(Self::capture_with_policy(
                        left, sources, retained, map, budget, policy,
                    )?),
                    right: Box::new(Self::capture_with_policy(
                        right, sources, retained, map, budget, policy,
                    )?),
                    negated: *negated,
                })
            }
            LogicValue::Word(word) => Ok(Self::Word(WordTemplate::capture_rebased(
                word, sources, retained, map, budget, policy,
            )?)),
            LogicValue::BoolComparison {
                word_type,
                comparison,
                left,
                right,
                negated,
            } => Ok(Self::Comparison {
                word_type: *word_type,
                comparison: *comparison,
                left: WordTemplate::capture_rebased(left, sources, retained, map, budget, policy)?,
                right: WordTemplate::capture_rebased(
                    right, sources, retained, map, budget, policy,
                )?,
                negated: *negated,
            }),
            _ => Self::capture(value, map, budget),
        }
    }
}

impl<A: Ord + Clone> WordTemplate<A> {
    fn capture_rebased<B: Ord + Clone>(
        word: &AffineValue<B>,
        sources: &[(A, AffineValue<B>)],
        retained: &[(A, AffineValue<B>)],
        map: &mut impl FnMut(&B, ScalarKind, &mut LogicBudget) -> Result<A, LogicError>,
        budget: &mut LogicBudget,
        policy: basis::SourcePolicy,
    ) -> Result<Self, LogicError> {
        budget.charge(1 + word.terms.len())?;
        if word.terms.len() > MAX_LINEAR_TERMS {
            return Err(LogicError::Budget);
        }
        let (constant, mut terms, residual) =
            basis::rebase(word.constant, &word.terms, sources, policy, budget)?;
        let (constant, fixed, residual) = basis::rebase(
            constant,
            &residual,
            retained,
            basis::SourcePolicy::Alternatives,
            budget,
        )?;
        for (key, coefficient) in fixed {
            let entry = terms.entry(key).or_default();
            *entry = entry.checked_add(coefficient).ok_or(LogicError::Overflow)?;
        }
        for (atom, coefficient) in residual {
            let key = map(&atom, ScalarKind::Word, budget)?;
            let entry = terms.entry(key).or_default();
            *entry = entry.checked_add(coefficient).ok_or(LogicError::Overflow)?;
        }
        terms.retain(|_, c| *c != 0);
        if terms.len() > MAX_LINEAR_TERMS {
            return Err(LogicError::Budget);
        }
        Ok(Self { constant, terms })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type Value = LogicValue<u32, ()>;
    fn x(id: u32) -> AffineValue<u32> {
        AffineValue::variable(id, 1, 2).unwrap()
    }
    #[test]
    fn coordinate_rewrite_preserves_capture_facts_without_reexecuting_arithmetic() {
        let source = x(1).add(&x(2)).unwrap();
        let value = Value::BoolComparison {
            word_type: WordType::Usize,
            comparison: WordComparison::LessEqual,
            left: AffineValue {
                lower: 3,
                upper: 3,
                ..source.clone()
            },
            right: AffineValue::exact(4),
            negated: false,
        };
        let rewritten: Value = ScalarTemplate::rebase_capture(
            &value,
            &[(90, source)],
            &mut |id, _, _| Ok(*id),
            &mut LogicBudget::default(),
        )
        .unwrap();
        assert_eq!(rewritten.known_boolean(), Some(true));
        let Value::BoolComparison { left, .. } = rewritten else {
            panic!()
        };
        assert_eq!((left.lower, left.upper, left.constant), (3, 3, 0));
        assert_eq!(left.terms, BTreeMap::from([(90, 1)]));
        let value = Value::BoolAtom {
            atom: 2,
            negated: true,
            known: Some(true),
        };
        let rewritten: Value = ScalarTemplate::rebase_capture(
            &value,
            &[],
            &mut |id, _, _| Ok(*id + 10),
            &mut LogicBudget::default(),
        )
        .unwrap();
        assert_eq!(
            rewritten,
            Value::BoolAtom {
                atom: 12,
                negated: true,
                known: Some(true)
            }
        );
    }

    fn capture(
        value: &Value,
        sources: &[(u32, AffineValue<u32>)],
    ) -> Result<ScalarTemplate<u32>, LogicError> {
        ScalarTemplate::capture_rebased(
            value,
            sources,
            &[],
            &mut |a, _, _| Ok(*a),
            &mut LogicBudget::default(),
        )
    }

    #[test]
    fn complete_sources_rebase_offsets_scales_sums_and_signed_comparisons() {
        for source in [
            x(1).add(&AffineValue::exact(1)).unwrap(),
            x(1).scale(2).unwrap(),
            x(1).add(&x(2)).unwrap(),
        ] {
            let target = source
                .scale(3)
                .unwrap()
                .add(&x(3))
                .unwrap()
                .add(&AffineValue::exact(2))
                .unwrap();
            let plan = capture(&Value::Word(target), &[(90, source.clone())]).unwrap();
            let expected = ScalarTemplate::Word(WordTemplate {
                constant: 2,
                terms: BTreeMap::from([(90, 3), (3, 1)]),
            });
            assert_eq!(plan, expected);
            let value = plan
                .instantiate(
                    &mut |id, _, _| {
                        Ok(Value::Word(AffineValue::variable(*id + 100, 2, 4).unwrap()))
                    },
                    &mut LogicBudget::default(),
                )
                .unwrap();
            let Value::Word(value) = value else { panic!() };
            assert_eq!((value.lower, value.upper), (10, 18));
            assert_eq!(value.terms, BTreeMap::from([(190, 3), (103, 1)]));
            let difference = AffineValue::exact(20).sub(&source).unwrap();
            let comparison = Value::BoolComparison {
                word_type: WordType::Usize,
                comparison: WordComparison::LessEqual,
                left: difference,
                right: AffineValue::exact(15),
                negated: true,
            };
            let plan = capture(&comparison, &[(90, source)]).unwrap();
            let ScalarTemplate::Comparison { left, negated, .. } = plan else {
                panic!()
            };
            assert!(negated);
            assert_eq!(
                left,
                WordTemplate {
                    constant: 20,
                    terms: BTreeMap::from([(90, -1)])
                }
            );
        }
    }

    #[test]
    fn domains_use_current_slots_and_do_not_reuse_old_source_ranges() {
        let source = x(1).add(&AffineValue::exact(1)).unwrap();
        let target = Value::Word(source.add(&AffineValue::exact(1)).unwrap());
        let plan = capture(&target, &[(90, source)]).unwrap();
        assert_eq!(
            plan.instantiate(
                &mut |_, _, _| Ok(Value::Word(AffineValue::variable(9, 0, u64::MAX).unwrap())),
                &mut LogicBudget::default()
            ),
            Err(LogicError::Overflow)
        );
    }

    #[test]
    fn independent_overlapping_sources_are_order_independent_and_fractional_matches_are_not_used() {
        let a = x(1).add(&AffineValue::exact(1)).unwrap();
        let b = x(1).add(&x(2)).unwrap();
        let target = Value::Word(b.clone());
        for sources in [
            vec![(90, a.clone()), (91, b.clone())],
            vec![(91, b.clone()), (90, a.clone())],
        ] {
            assert_eq!(
                capture(&target, &sources),
                Ok(ScalarTemplate::Word(WordTemplate {
                    constant: 0,
                    terms: BTreeMap::from([(91, 1)]),
                }))
            );
        }
        let source = x(1).scale(2).unwrap();
        assert_eq!(
            ScalarTemplate::<u32>::capture_rebased(
                &Value::Word(x(1)),
                &[(90, source)],
                &[],
                &mut |_, _, _| Err(LogicError::Unbound),
                &mut LogicBudget::default()
            ),
            Err(LogicError::Unbound)
        );
        // Distinct identities with identical bounds never match a source.
        assert_eq!(
            ScalarTemplate::<u32>::capture_rebased(
                &Value::Word(x(3)),
                &[(90, a)],
                &[],
                &mut |_, _, _| Err(LogicError::Unbound),
                &mut LogicBudget::default()
            ),
            Err(LogicError::Unbound)
        );
    }

    #[test]
    fn malformed_sources_host_overflow_and_budget_are_not_silent_fallbacks() {
        let source = x(1);
        let target = Value::Word(source.clone());
        assert_eq!(
            capture(&target, &[(90, source.clone()), (90, source.clone())]),
            Err(LogicError::InvalidNode)
        );
        let mut huge = source.clone();
        huge.constant = i128::MIN;
        assert_eq!(capture(&target, &[(90, huge)]), Err(LogicError::Overflow));
        let mut budget = LogicBudget::default();
        budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
        assert_eq!(
            ScalarTemplate::<u32>::capture_rebased(
                &target,
                &[(90, source)],
                &[],
                &mut |a, _, _| Ok(*a),
                &mut budget
            ),
            Err(LogicError::Budget)
        );
    }

    #[test]
    fn overlapping_fixed_residual_and_independent_changing_sources_reconstruct_identity() {
        let count = x(1)
            .add(&x(2))
            .unwrap()
            .add(&AffineValue::exact(1))
            .unwrap();
        let target = count.add(&x(2)).unwrap();
        let plan = capture(&Value::Word(target.clone()), &[(90, count.clone())]).unwrap();
        assert_eq!(
            plan,
            ScalarTemplate::Word(WordTemplate {
                constant: 0,
                terms: BTreeMap::from([(90, 1), (2, 1)]),
            })
        );
        // Neither the source's historical roots nor its entry range appear in
        // the template. A shared root survives only via an admitted leaf.
        assert_eq!(
            ScalarTemplate::<u32>::capture_rebased(
                &Value::Word(target.clone()),
                &[(90, count.clone())],
                &[],
                &mut |_, _, _| Err(LogicError::Unbound),
                &mut LogicBudget::default(),
            ),
            Err(LogicError::Unbound)
        );
        let Value::Word(restored) = plan
            .instantiate(
                &mut |id, _, _| Ok(Value::Word(if *id == 90 { count.clone() } else { x(*id) })),
                &mut LogicBudget::default(),
            )
            .unwrap()
        else {
            panic!()
        };
        assert_eq!(
            (restored.constant, restored.terms),
            (target.constant, target.terms)
        );

        let other = x(2)
            .add(&x(3))
            .unwrap()
            .add(&AffineValue::exact(2))
            .unwrap();
        let target = Value::Word(count.scale(2).unwrap().add(&other).unwrap());
        for sources in [
            vec![(90, count.clone()), (91, other.clone())],
            vec![(91, other), (90, count)],
        ] {
            assert_eq!(
                capture(&target, &sources),
                Ok(ScalarTemplate::Word(WordTemplate {
                    constant: 0,
                    terms: BTreeMap::from([(90, 2), (91, 1)]),
                }))
            );
        }
    }

    #[test]
    fn dependent_coordinates_and_nonintegral_elimination_are_not_guessed() {
        let source = x(1).add(&x(2)).unwrap();
        for dependent in [
            source.clone(),
            source
                .scale(2)
                .unwrap()
                .add(&AffineValue::exact(1))
                .unwrap(),
        ] {
            for sources in [
                vec![(90, source.clone()), (91, dependent.clone())],
                vec![(91, dependent), (90, source.clone())],
            ] {
                assert_eq!(
                    capture(&Value::Word(source.clone()), &sources),
                    Err(LogicError::Unbound)
                );
            }
        }
        let fractional = x(1).scale(2).unwrap().add(&x(2)).unwrap();
        assert_eq!(
            capture(
                &Value::Word(source.clone()),
                &[(90, fractional), (91, source)]
            ),
            Err(LogicError::Unbound)
        );
        // Fixed atomic parameters are not rewritten through a source requiring
        // a root absent from the target, even when that root has a live alias.
        assert_eq!(
            capture(&Value::Word(x(2)), &[(90, x(1).add(&x(2)).unwrap())]),
            Ok(ScalarTemplate::Word(WordTemplate {
                constant: 0,
                terms: BTreeMap::from([(2, 1)])
            }))
        );
    }

    #[test]
    fn signed_elimination_uses_current_domains_and_shared_work_budget() {
        let a = x(1).add(&x(2)).unwrap();
        let b = x(1).add(&x(2).scale(2).unwrap()).unwrap();
        // x+y terms are both present, so the supported basis can also express
        // 3*x+y = 5*a-2*b. Each original source operation was checked separately.
        let target = Value::Word(x(1).scale(3).unwrap().add(&x(2)).unwrap());
        let sources = [(90, a), (91, b)];
        let plan = capture(&target, &sources).unwrap();
        assert_eq!(
            plan,
            ScalarTemplate::Word(WordTemplate {
                constant: 0,
                terms: BTreeMap::from([(90, 5), (91, -2)]),
            })
        );
        assert_eq!(
            plan.instantiate(
                &mut |id, _, _| Ok(Value::Word(AffineValue::exact(if *id == 90 {
                    1
                } else {
                    4
                }))),
                &mut LogicBudget::default(),
            ),
            Err(LogicError::Overflow)
        );
        let mut budget = LogicBudget::default();
        // Enough for initial shape admission, but not the elimination itself.
        budget.charge(MAX_SUBSTITUTION_NODES - 24).unwrap();
        assert_eq!(
            ScalarTemplate::<u32>::capture_rebased(
                &target,
                &sources,
                &[],
                &mut |a, _, _| Ok(*a),
                &mut budget,
            ),
            Err(LogicError::Budget)
        );
    }

    #[test]
    fn fixed_composite_sources_bind_residuals_without_atomic_root_inputs() {
        let changing = x(1).add(&AffineValue::exact(1)).unwrap();
        let fixed = x(2)
            .add(&x(3))
            .unwrap()
            .add(&AffineValue::exact(1))
            .unwrap();
        let target = Value::Word(changing.add(&fixed).unwrap());
        let plan = ScalarTemplate::capture_rebased(
            &target,
            &[(90, changing.clone())],
            &[(92, fixed.clone())],
            &mut |_, _, _| Err(LogicError::Unbound),
            &mut LogicBudget::default(),
        )
        .unwrap();
        assert_eq!(
            plan,
            ScalarTemplate::Word(WordTemplate {
                constant: 0,
                terms: BTreeMap::from([(90, 1), (92, 1)]),
            })
        );
        for retained in [
            vec![(92, fixed.clone()), (94, fixed.clone())],
            vec![(94, fixed.clone()), (92, fixed.clone())],
        ] {
            assert_eq!(
                ScalarTemplate::capture_rebased(
                    &target,
                    &[(90, changing.clone())],
                    &retained,
                    &mut |_, _, _| Err(LogicError::Unbound),
                    &mut LogicBudget::default(),
                )
                .unwrap(),
                plan
            );
        }
        // Same range, different identity is never a replacement.
        let unrelated = x(4)
            .add(&x(5))
            .unwrap()
            .add(&AffineValue::exact(1))
            .unwrap();
        assert_eq!(
            ScalarTemplate::capture_rebased(
                &target,
                &[(90, changing.clone())],
                &[(92, unrelated)],
                &mut |_, _, _| Err(LogicError::Unbound),
                &mut LogicBudget::default(),
            ),
            Err(LogicError::Unbound)
        );
        assert_eq!(
            ScalarTemplate::capture_rebased(
                &target,
                &[(90, changing)],
                &[(90, fixed)],
                &mut |_, _, _| Err(LogicError::Unbound),
                &mut LogicBudget::default(),
            ),
            Err(LogicError::InvalidNode)
        );
        assert_eq!(
            plan.instantiate(
                &mut |_, _, _| Ok(Value::Word(AffineValue::variable(8, 0, u64::MAX).unwrap())),
                &mut LogicBudget::default(),
            ),
            Err(LogicError::Overflow)
        );
    }
}
