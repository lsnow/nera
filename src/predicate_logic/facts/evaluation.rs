//! Checked evaluation of new scalar expressions under established premises.
//! Every arithmetic intermediate must be defined before a later cancellation.
use super::*;

impl<T: Copy + Eq, A: Ord + Clone, R: Clone + Eq> EstablishedFacts<T, A, R> {
    /// Preserve Boolean comparison identities while checking every numeric
    /// intermediate under the same premises. Reuse the capture evaluator for
    /// Boolean semantics after replacing only already checked scalar nodes.
    pub(crate) fn evaluate_scalar(
        &self,
        expression: &LogicExpression<T>,
        leaves: &ExpressionLeaves<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Option<TypedLogicValue<T, A, R>>, LogicError> {
        let Some((values, _)) = self.checked_terms(expression, leaves, budget)? else {
            return Ok(None);
        };
        let mut checked = expression.clone();
        let mut inputs = Vec::new();
        for (node, value) in checked.nodes.iter_mut().zip(values) {
            budget.charge(1)?;
            let value = match value {
                Some(Term::Word(word)) => Some(LogicValue::Word(word.into_word()?)),
                Some(Term::Bool(value)) => Some(value),
                None => None,
            };
            if let Some(value) = value {
                node.kind = LogicNodeKind::Binder(LogicBinder::Parameter(inputs.len() as u32));
                inputs.push(TypedLogicValue { ty: node.ty, value });
            }
        }
        // checked_terms validated the entire source DAG and checked every
        // arithmetic intermediate. Replacing a checked subtree can now leave
        // dead operands; remove only those generated leftovers before the
        // capture evaluator validates the reduced DAG. Source dead terms and
        // overflowing intermediates must never be pruned before checking.
        let checked = compact_checked_expression(checked, budget)?;
        checked
            .evaluate_for_capture(
                &inputs,
                &[],
                &mut |_, _, _, _| Err(LogicError::Unbound),
                &mut |_, _| Err(LogicError::Unbound),
                budget,
            )
            .map(Some)
    }

    /// Return a bounded scalar with its original affine identity. Unknown
    /// definedness is None; malformed input and budget failures remain errors.
    pub(crate) fn evaluate_word(
        &self,
        expression: &LogicExpression<T>,
        leaves: &ExpressionLeaves<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Option<TypedLogicValue<T, A, R>>, LogicError> {
        let Some((values, facts)) = self.checked_terms(expression, leaves, budget)? else {
            return Ok(None);
        };
        let ty = expression.nodes[expression.root as usize].ty;
        if !matches!(ty, LogicType::U64 | LogicType::Usize) {
            return Err(LogicError::TypeMismatch);
        }
        let Some(Term::Word(word)) = &values[expression.root as usize] else {
            return Ok(None);
        };
        // This API explicitly asks for the result's range (for example an
        // initialized prefix). Definedness alone does not supply that range.
        let mut word = word.clone();
        facts.refine_word(ty, &mut word, budget)?;
        Ok(Some(TypedLogicValue {
            ty,
            value: LogicValue::Word(AffineValue {
                constant: word.constant,
                terms: word.terms.clone(),
                lower: u64::try_from(word.lower).map_err(|_| LogicError::Unproved)?,
                upper: u64::try_from(word.upper).map_err(|_| LogicError::Unproved)?,
            }),
        }))
    }

    fn checked_terms(
        &self,
        expression: &LogicExpression<T>,
        leaves: &ExpressionLeaves<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Option<CheckedTerms<T, A, R>>, LogicError> {
        let mut facts = self.constraint_graph(&[], budget)?;
        facts.propagate(budget)?;
        let values = Self::checked_terms_in(expression, leaves, &facts, &mut Vec::new(), budget)?;
        Ok(values.map(|values| (values, facts)))
    }

    fn checked_terms_in(
        expression: &LogicExpression<T>,
        leaves: &ExpressionLeaves<T, A, R>,
        facts: &mixed::MixedGraph<T, A>,
        numeric: &mut Vec<(LogicType<T>, mixed::WordFacts<A>)>,
        budget: &mut LogicBudget,
    ) -> Result<Option<EvaluatedTerms<A, R>>, LogicError> {
        // Prepare leaves without evaluating new arithmetic. Each operation is
        // checked in source order; only unresolved domains need refinement.
        let mut values = Self::prepare(expression, leaves, false, budget)?;
        if leaves.iter().any(|(_, value)| value.is_none()) {
            return Ok(None);
        }
        // Domain consistency is mandatory even when cancellation makes the
        // result constant. Register all operands together without solving a
        // separate tight range for each one.
        for (node, value) in expression.nodes.iter().zip(&values) {
            if let Some(Term::Word(word)) = value {
                let index = if let Some(index) = numeric.iter().position(|(ty, _)| *ty == node.ty) {
                    index
                } else {
                    numeric.push((node.ty, facts.word_facts(node.ty, budget)?));
                    numeric.len() - 1
                };
                numeric[index].1.observe(word, budget)?;
            }
        }
        for (_, context) in numeric.iter_mut() {
            context.consistent(budget)?;
        }
        for (id, node) in expression.nodes.iter().enumerate() {
            budget.charge(1 + MAX_LINEAR_TERMS)?;
            let operands = match node.kind {
                LogicNodeKind::Add(a, b) | LogicNodeKind::Sub(a, b) => vec![a, b],
                LogicNodeKind::Scale { operand, .. } => vec![operand],
                _ => continue,
            };
            let evaluate = |values: &[Option<Term<A, R>>]| -> Result<LinearWord<A>, LogicError> {
                let word = |id: u32| match &values[id as usize] {
                    Some(Term::Word(word)) => Ok(word),
                    _ => Err(LogicError::Unbound),
                };
                match node.kind {
                    LogicNodeKind::Add(a, b) | LogicNodeKind::Sub(a, b) => {
                        word(a)?.combine(word(b)?, matches!(node.kind, LogicNodeKind::Sub(..)))
                    }
                    LogicNodeKind::Scale { operand, factor } => word(operand)?.scale(factor),
                    _ => unreachable!(),
                }
            };
            let defined =
                |word: &LinearWord<A>| word.lower >= 0 && word.upper <= i128::from(u64::MAX);
            let mut result = evaluate(&values);
            if let Err(error) = &result
                && !matches!(error, LogicError::Unbound | LogicError::Overflow)
            {
                return Err(*error);
            }
            if !result.as_ref().is_ok_and(defined) {
                let index = if let Some(index) = numeric.iter().position(|(ty, _)| *ty == node.ty) {
                    index
                } else {
                    numeric.push((node.ty, facts.word_facts(node.ty, budget)?));
                    numeric.len() - 1
                };
                let numeric = &mut numeric[index].1;
                // Query the complete affine operation first. For a difference
                // this keeps correlations that separate operand intervals lose.
                if let Ok(word) = &mut result {
                    numeric.refine(word, budget)?;
                }
                if !result.as_ref().is_ok_and(defined) {
                    // Independent operand bounds can establish a sum or avoid
                    // overflowing the mathematical host interval for scaling.
                    for operand in operands {
                        let Some(Term::Word(word)) = &mut values[operand as usize] else {
                            return Ok(None);
                        };
                        numeric.refine(word, budget)?;
                    }
                    result = evaluate(&values);
                    if let Ok(word) = &mut result
                        && !defined(word)
                    {
                        numeric.refine(word, budget)?;
                    }
                }
            }
            let word = match result {
                Ok(word) if defined(&word) => word,
                Ok(_) | Err(LogicError::Unbound | LogicError::Overflow) => return Ok(None),
                Err(error) => return Err(error),
            };
            values[id] = Some(Term::Word(word));
        }
        Ok(Some(values))
    }

    /// Discharge a new scalar constraint from immutable premises. Unlike
    /// `extend`, this checks definedness of every new arithmetic operation;
    /// algebraic cancellation must not hide an overflowing intermediate.
    pub(crate) fn proves(
        &self,
        expression: &LogicExpression<T>,
        leaves: &ExpressionLeaves<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<bool, LogicError> {
        Ok(self.proves_batch(&[(expression, leaves)], budget)?[0])
    }

    /// Check all proposed constraints against the same immutable premises.
    /// Query clauses are observations, never assumed truths, and cannot make
    /// one another's arithmetic defined.
    pub(crate) fn proves_batch(
        &self,
        batch: &[ExpressionInput<'_, T, A, R>],
        budget: &mut LogicBudget,
    ) -> Result<Vec<bool>, LogicError> {
        budget.charge(batch.len())?;
        if batch.len() > MAX_CONSTRAINTS {
            return Err(LogicError::Budget);
        }
        let mut graph = self.constraint_graph(&[], budget)?;
        graph.propagate(budget)?;
        let mut numeric = Vec::new();
        let mut clauses = Vec::new();
        for (expression, leaves) in batch {
            let values = Self::checked_terms_in(expression, leaves, &graph, &mut numeric, budget)?;
            if expression.nodes[expression.root as usize].ty != LogicType::Bool {
                return Err(LogicError::TypeMismatch);
            }
            clauses.push(
                values
                    .map(|values| clause::Clause::new(expression, &values, budget))
                    .transpose()?,
            );
        }
        let mut roots = Vec::new();
        for clause in &clauses {
            roots.push(match clause {
                Some(clause) => graph.insert_clause(clause, budget)?,
                None => None,
            });
        }
        graph.propagate(budget)?;
        roots
            .into_iter()
            .map(|root| match root {
                Some(root) => Ok(graph.forced(root, budget)? == Some(true)),
                None => Ok(false),
            })
            .collect()
    }
}

fn map_operands<T>(kind: &mut LogicNodeKind<T>, mut map: impl FnMut(u32) -> u32) {
    match kind {
        LogicNodeKind::Add(a, b)
        | LogicNodeKind::Sub(a, b)
        | LogicNodeKind::Equal(a, b)
        | LogicNodeKind::Less(a, b)
        | LogicNodeKind::LessEqual(a, b)
        | LogicNodeKind::And(a, b)
        | LogicNodeKind::Or(a, b) => {
            *a = map(*a);
            *b = map(*b);
        }
        LogicNodeKind::Not(a) | LogicNodeKind::Scale { operand: a, .. } => *a = map(*a),
        _ => {}
    }
}

/// Only called on a validated, topologically ordered expression after checked
/// substitutions. It is not an admission path for arbitrary source syntax.
fn compact_checked_expression<T>(
    mut expression: LogicExpression<T>,
    budget: &mut LogicBudget,
) -> Result<LogicExpression<T>, LogicError> {
    budget.charge(expression.nodes.len().saturating_mul(2))?;
    let mut live = vec![false; expression.nodes.len()];
    live[expression.root as usize] = true;
    for (id, node) in expression.nodes.iter_mut().enumerate().rev() {
        if live[id] {
            map_operands(&mut node.kind, |operand| {
                live[operand as usize] = true;
                operand
            });
        }
    }
    let mut renames = vec![None; live.len()];
    let mut nodes = Vec::new();
    for (id, mut node) in expression.nodes.into_iter().enumerate() {
        if live[id] {
            map_operands(&mut node.kind, |operand| {
                renames[operand as usize].expect("retained checked operand")
            });
            renames[id] = Some(nodes.len() as u32);
            nodes.push(node);
        }
    }
    Ok(LogicExpression {
        root: renames[expression.root as usize].expect("retained checked root"),
        nodes,
    })
}
