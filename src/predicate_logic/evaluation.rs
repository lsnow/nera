//! One checked DAG evaluator, with separate value and capture policies.
//! Capture retains supported expression shapes, never runtime slot identities.
use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum EvaluationMode {
    Value,
    Capture,
}

impl EvaluationMode {
    fn word_comparison<A: Ord + Clone, R: Clone>(
        self,
        word_type: WordType,
        comparison: WordComparison,
        left: AffineValue<A>,
        right: AffineValue<A>,
        negated: bool,
    ) -> LogicValue<A, R> {
        if self == Self::Capture && (!left.terms.is_empty() || !right.terms.is_empty()) {
            LogicValue::BoolComparison {
                word_type,
                comparison,
                left,
                right,
                negated,
            }
        } else {
            LogicValue::word_comparison(word_type, comparison, left, right, negated)
        }
    }

    fn bool_equality<A: Ord + Clone, R: Clone>(
        self,
        a: &LogicValue<A, R>,
        b: &LogicValue<A, R>,
        budget: &mut LogicBudget,
    ) -> Result<LogicValue<A, R>, LogicError> {
        if self == Self::Value {
            return match a.bool_equal(b) {
                Some(value) => Ok(LogicValue::Bool(Some(value))),
                None => self.boolean_binary(BooleanOperation::Equal, a, b, budget),
            };
        }
        Ok(match (a, b) {
            (LogicValue::Bool(Some(value)), other) | (other, LogicValue::Bool(Some(value))) => {
                if *value {
                    other.clone()
                } else {
                    other.bool_not()
                }
            }
            _ => match capture_identity(a, b) {
                Some(value) => LogicValue::Bool(Some(value)),
                None => {
                    return LogicValue::boolean_binary(
                        BooleanOperation::Equal,
                        a.clone(),
                        b.clone(),
                        false,
                        budget,
                    );
                }
            },
        })
    }

    fn bool_combine<A: Ord + Clone, R: Clone>(
        self,
        a: &LogicValue<A, R>,
        b: &LogicValue<A, R>,
        is_or: bool,
        budget: &mut LogicBudget,
    ) -> Result<LogicValue<A, R>, LogicError> {
        if self == Self::Value {
            let value = a.bool_combine(b, is_or);
            return if matches!(value, LogicValue::Bool(None)) {
                self.boolean_binary(
                    if is_or {
                        BooleanOperation::Or
                    } else {
                        BooleanOperation::And
                    },
                    a,
                    b,
                    budget,
                )
            } else {
                Ok(value)
            };
        }
        Ok(match (a, b) {
            (LogicValue::Bool(Some(v)), _) if *v == is_or => a.clone(),
            (_, LogicValue::Bool(Some(v))) if *v == is_or => b.clone(),
            (LogicValue::Bool(Some(_)), _) => b.clone(),
            (_, LogicValue::Bool(Some(_))) => a.clone(),
            _ => match capture_identity(a, b) {
                Some(true) => a.clone(),
                Some(false) => LogicValue::Bool(Some(is_or)),
                None => {
                    return LogicValue::boolean_binary(
                        if is_or {
                            BooleanOperation::Or
                        } else {
                            BooleanOperation::And
                        },
                        a.clone(),
                        b.clone(),
                        false,
                        budget,
                    );
                }
            },
        })
    }

    fn boolean_binary<A: Ord + Clone, R: Clone>(
        self,
        operation: BooleanOperation,
        a: &LogicValue<A, R>,
        b: &LogicValue<A, R>,
        budget: &mut LogicBudget,
    ) -> Result<LogicValue<A, R>, LogicError> {
        match LogicValue::boolean_binary(operation, a.clone(), b.clone(), false, budget) {
            // Anonymous unknowns may still be queried, but cannot become a
            // reusable capture identity just because their trees look alike.
            Err(LogicError::Unbound) if self == Self::Value => Ok(LogicValue::Bool(None)),
            result => result,
        }
    }
}

/// Only exact symbolic shapes justify capture rewrites. Equal current values
/// or intervals cannot make two expressions interchangeable after induction.
fn capture_identity<A: Ord + Clone, R: Clone>(
    a: &LogicValue<A, R>,
    b: &LogicValue<A, R>,
) -> Option<bool> {
    let same_word =
        |a: &AffineValue<A>, b: &AffineValue<A>| a.constant == b.constant && a.terms == b.terms;
    match (a, b) {
        (
            LogicValue::BoolBinary {
                operation: a,
                left: al,
                right: ar,
                negated: an,
            },
            LogicValue::BoolBinary {
                operation: b,
                left: bl,
                right: br,
                negated: bn,
            },
        ) if a == b
            && capture_identity(al, bl) == Some(true)
            && capture_identity(ar, br) == Some(true) =>
        {
            Some(an == bn)
        }
        (LogicValue::Bool(Some(a)), LogicValue::Bool(Some(b))) => Some(a == b),
        (
            LogicValue::BoolAtom {
                atom: a,
                negated: x,
                ..
            },
            LogicValue::BoolAtom {
                atom: b,
                negated: y,
                ..
            },
        ) if a == b => Some(x == y),
        (
            LogicValue::BoolComparison {
                word_type: at,
                comparison: a,
                left: al,
                right: ar,
                negated: an,
            },
            LogicValue::BoolComparison {
                word_type: bt,
                comparison: b,
                left: bl,
                right: br,
                negated: bn,
            },
        ) if at == bt
            && a == b
            && ((same_word(al, bl) && same_word(ar, br))
                || (*a == WordComparison::Equal && same_word(al, br) && same_word(ar, bl))) =>
        {
            Some(an == bn)
        }
        _ => None,
    }
}

impl<T: Copy + Eq> LogicExpression<T> {
    /// Resolve leaves exactly once before evaluating operations. This is pure:
    /// only the adapter can resolve an actual resource or a permitted memory
    /// observation. Anonymous unknown Bool has no identity; named atoms are bounded literals.
    pub fn evaluate<A: Ord + Clone, R: Clone + Eq>(
        &self,
        parameters: &[TypedLogicValue<T, A, R>],
        existentials: &[TypedLogicValue<T, A, R>],
        observe: &mut impl FnMut(
            u32,
            u64,
            T,
            ObservationTime,
        ) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        resource: &mut impl FnMut(u32, &[u64]) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<TypedLogicValue<T, A, R>, LogicError> {
        self.evaluate_with_mode(
            parameters,
            existentials,
            observe,
            resource,
            budget,
            EvaluationMode::Value,
        )
    }

    /// Capture comparisons over identified words even when their current truth
    /// is known. This selects a shape only; adapters still prove every binding.
    pub(crate) fn evaluate_for_capture<A: Ord + Clone, R: Clone + Eq>(
        &self,
        parameters: &[TypedLogicValue<T, A, R>],
        existentials: &[TypedLogicValue<T, A, R>],
        observe: &mut impl FnMut(
            u32,
            u64,
            T,
            ObservationTime,
        ) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        resource: &mut impl FnMut(u32, &[u64]) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<TypedLogicValue<T, A, R>, LogicError> {
        self.evaluate_with_mode(
            parameters,
            existentials,
            observe,
            resource,
            budget,
            EvaluationMode::Capture,
        )
    }

    fn evaluate_with_mode<A: Ord + Clone, R: Clone + Eq>(
        &self,
        parameters: &[TypedLogicValue<T, A, R>],
        existentials: &[TypedLogicValue<T, A, R>],
        observe: &mut impl FnMut(
            u32,
            u64,
            T,
            ObservationTime,
        ) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        resource: &mut impl FnMut(u32, &[u64]) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        budget: &mut LogicBudget,
        mode: EvaluationMode,
    ) -> Result<TypedLogicValue<T, A, R>, LogicError> {
        if self.nodes.is_empty()
            || self.nodes.len() > MAX_EXPRESSION_NODES
            || self.root as usize + 1 != self.nodes.len()
        {
            return Err(LogicError::Budget);
        }
        for input in parameters.iter().chain(existentials) {
            input.value.capture_leaves(budget)?;
        }
        let mut leaves = BTreeMap::new();
        for (index, node) in self.nodes.iter().enumerate() {
            let value = match &node.kind {
                LogicNodeKind::Observe {
                    resource,
                    offset,
                    access,
                    time,
                } => Some(observe(*resource, *offset, *access, *time)?),
                LogicNodeKind::Resource {
                    resource: index,
                    path,
                } => Some(resource(*index, path)?),
                _ => None,
            };
            if let Some(value) = value {
                if value.ty != node.ty {
                    return Err(LogicError::TypeMismatch);
                }
                leaves.insert(index, value);
            }
        }
        let parameter_types = parameters.iter().map(|v| v.ty).collect::<Vec<_>>();
        let existential_types = existentials.iter().map(|v| v.ty).collect::<Vec<_>>();
        self.validate(
            &parameter_types,
            &existential_types,
            &|r, o, a, t| {
                self.nodes
                    .iter()
                    .enumerate()
                    .find_map(|(i, n)| match &n.kind {
                        LogicNodeKind::Observe {
                            resource,
                            offset,
                            access,
                            time,
                        } if (*resource, *offset, *access, *time) == (r, o, a, t) => {
                            leaves.get(&i).map(|v| v.ty)
                        }
                        _ => None,
                    })
            },
            &|r, p| {
                self.nodes
                    .iter()
                    .enumerate()
                    .find_map(|(i, n)| match &n.kind {
                        LogicNodeKind::Resource { resource, path }
                            if *resource == r && path == p =>
                        {
                            match leaves.get(&i)?.ty {
                                LogicType::Resource(t) => Some(t),
                                _ => None,
                            }
                        }
                        _ => None,
                    })
            },
            budget,
        )?;
        let mut values = Vec::<TypedLogicValue<T, A, R>>::new();
        for (index, node) in self.nodes.iter().enumerate() {
            let get = |id: u32| values.get(id as usize).ok_or(LogicError::InvalidNode);
            let word = |id: u32| match &get(id)?.value {
                LogicValue::Word(v) => Ok(v.clone()),
                _ => Err(LogicError::TypeMismatch),
            };
            let boolean = |id: u32| match &get(id)?.value {
                v @ (LogicValue::Bool(_)
                | LogicValue::BoolAtom { .. }
                | LogicValue::BoolComparison { .. }
                | LogicValue::BoolBinary { .. }) => Ok(v.clone()),
                _ => Err(LogicError::TypeMismatch),
            };
            let value = match &node.kind {
                LogicNodeKind::Word(v) => LogicValue::Word(AffineValue::exact(*v)),
                LogicNodeKind::Bool(v) => LogicValue::Bool(Some(*v)),
                LogicNodeKind::Binder(LogicBinder::Parameter(id)) => parameters
                    .get(*id as usize)
                    .ok_or(LogicError::Unbound)?
                    .value
                    .clone(),
                LogicNodeKind::Binder(LogicBinder::Existential(id)) => existentials
                    .get(*id as usize)
                    .ok_or(LogicError::Unbound)?
                    .value
                    .clone(),
                LogicNodeKind::Observe { .. } | LogicNodeKind::Resource { .. } => {
                    leaves.remove(&index).ok_or(LogicError::InvalidNode)?.value
                }
                LogicNodeKind::Add(a, b) => LogicValue::Word(word(*a)?.add(&word(*b)?)?),
                LogicNodeKind::Sub(a, b) => LogicValue::Word(word(*a)?.sub(&word(*b)?)?),
                LogicNodeKind::Scale { operand, factor } => {
                    LogicValue::Word(word(*operand)?.scale(*factor)?)
                }
                LogicNodeKind::Equal(a, b) => match (&get(*a)?.value, &get(*b)?.value) {
                    (LogicValue::Word(left), LogicValue::Word(right)) => mode.word_comparison(
                        WordType::from_logic_type(get(*a)?.ty)?,
                        WordComparison::Equal,
                        left.clone(),
                        right.clone(),
                        false,
                    ),
                    (
                        a @ (LogicValue::Bool(_)
                        | LogicValue::BoolAtom { .. }
                        | LogicValue::BoolComparison { .. }
                        | LogicValue::BoolBinary { .. }),
                        b @ (LogicValue::Bool(_)
                        | LogicValue::BoolAtom { .. }
                        | LogicValue::BoolComparison { .. }
                        | LogicValue::BoolBinary { .. }),
                    ) => mode.bool_equality(a, b, budget)?,
                    (LogicValue::Resource(a), LogicValue::Resource(b)) => {
                        LogicValue::Bool(Some(a == b))
                    }
                    (
                        LogicValue::ResourceAtom { atom: a },
                        LogicValue::ResourceAtom { atom: b },
                    ) => LogicValue::Bool((a == b).then_some(true)),
                    (LogicValue::ResourceAtom { .. }, LogicValue::Resource(_))
                    | (LogicValue::Resource(_), LogicValue::ResourceAtom { .. }) => {
                        LogicValue::Bool(None)
                    }
                    _ => return Err(LogicError::TypeMismatch),
                },
                LogicNodeKind::Less(a, b) => mode.word_comparison(
                    WordType::from_logic_type(get(*a)?.ty)?,
                    WordComparison::LessEqual,
                    word(*b)?,
                    word(*a)?,
                    true,
                ),
                LogicNodeKind::LessEqual(a, b) => mode.word_comparison(
                    WordType::from_logic_type(get(*a)?.ty)?,
                    WordComparison::LessEqual,
                    word(*a)?,
                    word(*b)?,
                    false,
                ),
                LogicNodeKind::Not(a) => boolean(*a)?.bool_not(),
                LogicNodeKind::And(a, b) => {
                    mode.bool_combine(&boolean(*a)?, &boolean(*b)?, false, budget)?
                }
                LogicNodeKind::Or(a, b) => {
                    mode.bool_combine(&boolean(*a)?, &boolean(*b)?, true, budget)?
                }
            };
            let matches = matches!(
                (&node.ty, &value),
                (LogicType::U64 | LogicType::Usize, LogicValue::Word(_))
                    | (
                        LogicType::Bool,
                        LogicValue::Bool(_)
                            | LogicValue::BoolAtom { .. }
                            | LogicValue::BoolComparison { .. }
                            | LogicValue::BoolBinary { .. }
                    )
                    | (
                        LogicType::Resource(_),
                        LogicValue::Resource(_) | LogicValue::ResourceAtom { .. }
                    )
            );
            if !matches {
                return Err(LogicError::TypeMismatch);
            }
            let value = if mode == EvaluationMode::Value {
                value
                    .known_boolean()
                    .map_or(value, |known| LogicValue::Bool(Some(known)))
            } else {
                value
            };
            values.push(TypedLogicValue { ty: node.ty, value });
        }
        values.pop().ok_or(LogicError::InvalidNode)
    }
}
