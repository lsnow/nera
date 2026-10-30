//! Leaf capture is the boundary between actual resource observations and pure
//! expression reasoning. Capturing a leaf does not establish a constraint.
use super::*;

impl ResourceState {
    /// Observe one actual runtime scalar using its existing provenance or a
    /// surviving immutable alias. This creates no binder or resource evidence.
    pub(in crate::verifier::resource::predicate) fn predicate_scalar_input(
        &self,
        scope: InstanceScope,
        ty: LogicType<VirMemoryAccess>,
        id: VirValueId,
        aliases: &BTreeMap<VirValueId, LocalSnapshot>,
    ) -> Result<PredicateLogicValue, PredicateError> {
        let fallback = aliases.get(&id).copied().map_or(
            ObservationAtom::Current { scope, value: id },
            LocalSnapshot::atom,
        );
        let value = match (ty, self.value(id)) {
            (LogicType::U64 | LogicType::Usize, Some(AbstractValue::U64(value))) => {
                LogicValue::Word(
                    observed_scalar_word(scope, *value, self.word_origin(id), fallback)
                        .map_err(map_error)?,
                )
            }
            (LogicType::Bool, Some(AbstractValue::Bool(value))) => {
                observed_scalar_bool(scope, *value, self.bool_origin(id), Some(fallback))
            }
            _ => return Err(PredicateError::InvalidBinding),
        };
        Ok(TypedLogicValue { ty, value })
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Keep boundary identities, state, evidence and shared budget explicit at the resource adapter"
    )]
    pub(super) fn capture_predicate_logic_leaves(
        &self,
        definition: &PredicateDefinition,
        resources: &[SealedResource],
        scope: InstanceScope,
        parameters: &[PredicateLogicValue],
        witnesses: &[PredicateLogicValue],
        expression: &LogicExpression<VirMemoryAccess>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<(u32, PredicateLogicValue)>, PredicateError> {
        // Charge both the retained syntax and each substituted leaf. Repeated
        // constraints do not get separate budgets.
        budget.charge(expression.nodes.len()).map_err(map_error)?;
        let mut leaves = Vec::new();
        for (index, node) in expression.nodes.iter().enumerate() {
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
            .evaluate(
                parameters,
                witnesses,
                &mut |r, o, a, t| {
                    self.observe_predicate_logic(definition, resources, scope, false, (r, o, a, t))
                },
                &mut |r, path| resource_value(self, definition, resources, r, path),
                budget,
            )
            .map_err(map_error)?;
            // A saved leaf is an immutable expression identity. Current truth
            // is imported separately by fact_inputs when premises are used.
            leaves.push((index as u32, value));
        }
        Ok(leaves)
    }
}

/// Observe a value whose scalar origin was retained by checked transfers. This
/// does not execute the origin expression again: its original root intervals
/// can be wider than the premises that made the actual computation safe.
/// New source arithmetic still goes through the ordinary definedness checks.
pub(super) fn observed_word(
    scope: InstanceScope,
    value: U64Interval,
    origin: Option<ScalarOrigin>,
    fallback: ObservationAtom,
) -> Result<AffineValue<ObservationAtom>, LogicError> {
    word_observation(scope, value, origin, fallback, false)
}

/// Actual scalar inputs keep their existing identity through singleton
/// refinement. Literal expression nodes still use AffineValue::exact.
pub(super) fn observed_scalar_word(
    scope: InstanceScope,
    value: U64Interval,
    origin: Option<ScalarOrigin>,
    fallback: ObservationAtom,
) -> Result<AffineValue<ObservationAtom>, LogicError> {
    word_observation(scope, value, origin, fallback, true)
}

/// Both observation policies describe the same immutable origin. Matching
/// compares the full symbolic shape under either policy, never just its range.
pub(super) fn matches_word_origin(
    scope: InstanceScope,
    origin: ScalarOrigin,
    saved: &AffineValue<ObservationAtom>,
) -> bool {
    [true, false].into_iter().any(|retain_identity| {
        word_observation(
            scope,
            U64Interval::unknown(),
            Some(origin),
            ObservationAtom::Historical {
                scope,
                cell: origin.first,
                local: true,
            },
            retain_identity,
        )
        .is_ok_and(|candidate| {
            candidate.constant == saved.constant && candidate.terms == saved.terms
        })
    })
}

fn word_observation(
    mut scope: InstanceScope,
    value: U64Interval,
    origin: Option<ScalarOrigin>,
    fallback: ObservationAtom,
    retain_identity: bool,
) -> Result<AffineValue<ObservationAtom>, LogicError> {
    let Some(origin) = origin else {
        return if retain_identity {
            AffineValue::identified(fallback, value.lower(), value.upper())
        } else {
            AffineValue::variable(fallback, value.lower(), value.upper())
        };
    };
    scope.opening = 0;
    if origin
        .terms()
        .any(|(cell, _)| cell.initial_lower > cell.initial_upper)
    {
        return Err(LogicError::InvalidNode);
    }
    // The existing value is a word. Saturating the historical upper envelope
    // does not prove a new operation safe; it merely bounds this observed word.
    let initial = origin.initial_interval().ok_or(LogicError::Unproved)?;
    let lower = initial.lower().max(value.lower());
    let upper = initial.upper().min(value.upper());
    if lower > upper {
        return Err(LogicError::Unproved);
    }
    let mut constant = i128::from(origin.addend);
    let mut terms = BTreeMap::<ObservationAtom, i128>::new();
    for (cell, coefficient) in origin.terms() {
        if coefficient == 0 {
            continue;
        }
        let coefficient = i128::from(coefficient);
        if !retain_identity && cell.initial_lower == cell.initial_upper {
            constant = constant
                .checked_add(
                    i128::from(cell.initial_lower)
                        .checked_mul(coefficient)
                        .ok_or(LogicError::Overflow)?,
                )
                .ok_or(LogicError::Overflow)?;
        } else {
            let entry = terms
                .entry(ObservationAtom::Historical {
                    scope,
                    cell,
                    local: true,
                })
                .or_default();
            *entry = entry.checked_add(coefficient).ok_or(LogicError::Overflow)?;
        }
    }
    Ok(AffineValue {
        constant,
        terms,
        lower,
        upper,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn source() -> ScalarOrigin {
        ScalarOrigin {
            first: crate::verifier::resource::ScalarOriginCell {
                root: crate::verifier::resource::ScalarOriginRoot::Parameter {
                    function: crate::VirFunctionId::new(0),
                    value: VirValueId::new(3),
                },
                initial_lower: 0,
                initial_upper: u64::MAX,
            },
            scale: 2,
            second: None,
            addend: 1,
        }
    }
    #[test]
    fn exact_scalar_sources_remain_identified_without_changing_memory_observations() {
        let scope = InstanceScope {
            declaration: 0,
            instance: 4,
            opening: 0,
        };
        let atom = ObservationAtom::Local {
            scope,
            value: VirValueId::new(90),
        };
        let literal = observed_word(scope, U64Interval::exact(0), None, atom.clone()).unwrap();
        assert_eq!(literal, AffineValue::exact(0));
        let scalar =
            observed_scalar_word(scope, U64Interval::exact(0), None, atom.clone()).unwrap();
        assert_eq!(scalar.terms, BTreeMap::from([(atom.clone(), 1)]));
        let mut origin = source();
        origin.first.initial_lower = 2;
        origin.first.initial_upper = 2;
        let scalar =
            observed_scalar_word(scope, U64Interval::exact(5), Some(origin), atom.clone()).unwrap();
        assert_eq!((scalar.lower, scalar.upper, scalar.constant), (5, 5, 1));
        assert_eq!(
            scalar.terms,
            BTreeMap::from([(
                ObservationAtom::Historical {
                    scope,
                    cell: origin.first,
                    local: true
                },
                2
            )])
        );
        assert!(matches_word_origin(scope, origin, &scalar));
        let mut different = origin;
        different.first.root = crate::verifier::resource::ScalarOriginRoot::Parameter {
            function: crate::VirFunctionId::new(1),
            value: VirValueId::new(3),
        };
        assert!(!matches_word_origin(scope, different, &scalar));
        assert_eq!(
            observed_word(scope, U64Interval::exact(5), Some(origin), atom.clone()).unwrap(),
            AffineValue::exact(5)
        );
        assert_eq!(
            observed_scalar_word(scope, U64Interval::exact(4), Some(origin), atom),
            Err(LogicError::Unproved)
        );
    }
    #[test]
    fn observing_checked_composite_values_does_not_reexecute_wide_root_arithmetic() {
        let scope = InstanceScope {
            declaration: 0,
            instance: 4,
            opening: 9,
        };
        let fallback = ObservationAtom::Current {
            scope,
            value: VirValueId::new(10),
        };
        let result = observed_word(
            scope,
            U64Interval::new(1, 7).unwrap(),
            Some(source()),
            fallback.clone(),
        )
        .unwrap();
        assert_eq!((result.lower, result.upper, result.constant), (1, 7, 1));
        assert_eq!(result.terms.len(), 1);
        let (
            ObservationAtom::Historical {
                scope: captured, ..
            },
            coefficient,
        ) = result.terms.first_key_value().unwrap()
        else {
            panic!()
        };
        assert_eq!(captured.opening, 0);
        assert_eq!(*coefficient, 2);
        let mut sum = source();
        let mut other = sum.first;
        other.root = crate::verifier::resource::ScalarOriginRoot::Parameter {
            function: crate::VirFunctionId::new(0),
            value: VirValueId::new(5),
        };
        sum.second = Some((other, 1));
        let result = observed_word(
            scope,
            U64Interval::new(1, 9).unwrap(),
            Some(sum),
            fallback.clone(),
        )
        .unwrap();
        assert_eq!(result.terms.len(), 2);
        let wide = observed_word(scope, U64Interval::unknown(), Some(sum), fallback).unwrap();
        assert_eq!(wide.add(&AffineValue::exact(1)), Err(LogicError::Overflow));
        let mut impossible = source();
        impossible.first.initial_lower = 5;
        assert_eq!(
            observed_word(
                scope,
                U64Interval::new(0, 3).unwrap(),
                Some(impossible),
                ObservationAtom::Current {
                    scope,
                    value: VirValueId::new(10)
                }
            ),
            Err(LogicError::Unproved)
        );
    }
}

/// Memory observations may collapse known values. Actual scalar captures keep
/// provenance and truth separately so induction never depends on entry truth.
pub(super) fn observed_bool(
    scope: InstanceScope,
    value: AbstractBool,
    origin: Option<BoolOrigin>,
    fallback: Option<ObservationAtom>,
) -> LogicValue<ObservationAtom, ResourceWitness> {
    bool_observation(scope, value, origin, fallback, false)
}

pub(super) fn observed_scalar_bool(
    scope: InstanceScope,
    value: AbstractBool,
    origin: Option<BoolOrigin>,
    fallback: Option<ObservationAtom>,
) -> LogicValue<ObservationAtom, ResourceWitness> {
    bool_observation(scope, value, origin, fallback, true)
}

fn bool_observation(
    mut scope: InstanceScope,
    value: AbstractBool,
    origin: Option<BoolOrigin>,
    fallback: Option<ObservationAtom>,
    retain_identity: bool,
) -> LogicValue<ObservationAtom, ResourceWitness> {
    let known = match value {
        AbstractBool::True => Some(true),
        AbstractBool::False => Some(false),
        AbstractBool::Unknown => None,
    };
    if known.is_some() && !retain_identity {
        return LogicValue::Bool(known);
    }
    scope.opening = 0;
    let atom = origin
        .map(|origin| ObservationAtom::HistoricalBool {
            scope,
            origin,
            local: true,
        })
        .or(fallback);
    match atom {
        Some(atom) => LogicValue::BoolAtom {
            atom,
            negated: false,
            known,
        },
        None => LogicValue::Bool(known),
    }
}

#[cfg(test)]
mod boolean_tests {
    use super::*;

    #[test]
    fn known_boolean_scalar_observations_preserve_actual_origins_only() {
        let scope = InstanceScope {
            declaration: 0,
            instance: 4,
            opening: 9,
        };
        let origin = BoolOrigin::Parameter {
            function: crate::VirFunctionId::new(1),
            value: VirValueId::new(3),
        };
        let fallback = ObservationAtom::Local {
            scope,
            value: VirValueId::new(90),
        };
        for (value, known) in [
            (AbstractBool::True, Some(true)),
            (AbstractBool::False, Some(false)),
            (AbstractBool::Unknown, None),
        ] {
            let local = observed_scalar_bool(scope, value, None, Some(fallback.clone()));
            assert_eq!(
                local,
                LogicValue::BoolAtom {
                    atom: fallback.clone(),
                    negated: false,
                    known
                }
            );
            let historical =
                observed_scalar_bool(scope, value, Some(origin), Some(fallback.clone()));
            assert_eq!(
                historical,
                LogicValue::BoolAtom {
                    atom: ObservationAtom::HistoricalBool {
                        scope: InstanceScope {
                            opening: 0,
                            ..scope
                        },
                        origin,
                        local: true
                    },
                    negated: false,
                    known,
                }
            );
            assert_eq!(
                observed_scalar_bool(scope, value, None, None),
                LogicValue::Bool(known)
            );
            let memory = observed_bool(scope, value, Some(origin), Some(fallback.clone()));
            assert_eq!(
                memory,
                if known.is_some() {
                    LogicValue::Bool(known)
                } else {
                    historical
                }
            );
        }
    }
}
