//! Bounded consequences of already established, immutable constraint snapshots.
//!
//! This module knows no VIR, allocations, permissions, SSA values or instance
//! lifetimes. The adapter must establish each premise and resolve its leaves;
//! an unavailable/stale observation is supplied as `None`. This is a pure
//! reasoning service, not a proof certificate checker or a source of authority.
use super::*;
mod boolean;
mod candidates;
mod clause;
mod evaluation;
mod linear;
mod mixed;
mod offsets;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Comparison {
    Equal,
    Less,
    LessEqual,
}

use super::affine::LinearWord;

#[derive(Clone)]
enum Term<A: Ord, R> {
    Word(LinearWord<A>),
    Bool(LogicValue<A, R>),
}

enum Fact<T, A: Ord, R> {
    Compare(LogicType<T>, Comparison, Term<A, R>, Term<A, R>),
    Boolean(LogicValue<A, R>, bool),
    Clause(clause::Clause<T, A, R>),
}

pub(crate) type DifferenceObservation<T, A, R> =
    (TypedLogicValue<T, A, R>, TypedLogicValue<T, A, R>, i128);

/// Node-indexed observations; a missing leaf never becomes an assumed premise.
pub(crate) type ExpressionLeaves<T, A, R> = [(u32, Option<TypedLogicValue<T, A, R>>)];
type ExpressionInput<'a, T, A, R> = (&'a LogicExpression<T>, &'a ExpressionLeaves<T, A, R>);
type EvaluatedTerms<A, R> = Vec<Option<Term<A, R>>>;
type CheckedTerms<T, A, R> = (EvaluatedTerms<A, R>, mixed::MixedGraph<T, A>);
type NumericPremise<A> = (Comparison, LinearWord<A>, LinearWord<A>);

pub(crate) struct EstablishedFacts<T, A: Ord, R> {
    facts: Vec<Fact<T, A, R>>,
    // Only successfully checked premises enter this graph. Queries clone it,
    // so proposed clauses and operand domains cannot become saved premises.
    prepared: mixed::MixedGraph<T, A>,
}

impl<T: Copy + Eq, A: Ord + Clone, R: Clone + Eq> EstablishedFacts<T, A, R> {
    pub(crate) fn new() -> Self {
        Self {
            facts: Vec::new(),
            prepared: mixed::MixedGraph::new(),
        }
    }

    /// Import Boolean observations established by the caller, preserving the
    /// supplied symbolic expressions. No runtime/source authority is created.
    /// The whole batch is checked before any observation becomes a premise.
    #[cfg(test)]
    pub(crate) fn extend_booleans(
        &mut self,
        observations: &[(TypedLogicValue<T, A, R>, bool)],
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        self.extend_observations(observations, &[], budget)
    }

    /// Publish numeric and Boolean observations as one transaction. These are
    /// established caller inputs, not hypotheses of the package being checked.
    pub(crate) fn extend_observations(
        &mut self,
        booleans: &[(TypedLogicValue<T, A, R>, bool)],
        differences: &[DifferenceObservation<T, A, R>],
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        self.extend_inputs(booleans, differences, &[], budget)
    }

    fn observation_additions(
        &self,
        booleans: &[(TypedLogicValue<T, A, R>, bool)],
        differences: &[DifferenceObservation<T, A, R>],
        budget: &mut LogicBudget,
    ) -> Result<Vec<Fact<T, A, R>>, LogicError> {
        budget.charge(booleans.len() + differences.len())?;
        if booleans.len() + differences.len() > MAX_EXPRESSION_NODES {
            return Err(LogicError::Budget);
        }
        let mut additions = Vec::new();
        for (value, truth) in booleans {
            validate_value(value, budget)?;
            if value.ty != LogicType::Bool {
                return Err(LogicError::TypeMismatch);
            }
            additions.push(Fact::Boolean(value.value.clone(), *truth));
        }
        for (left, right, bound) in differences {
            budget.charge(MAX_LINEAR_TERMS)?;
            validate_value(left, budget)?;
            validate_value(right, budget)?;
            if left.ty != right.ty || !matches!(left.ty, LogicType::U64 | LogicType::Usize) {
                return Err(LogicError::TypeMismatch);
            }
            let (LogicValue::Word(a), LogicValue::Word(b)) = (&left.value, &right.value) else {
                return Err(LogicError::TypeMismatch);
            };
            let a = LinearWord::from_word(a);
            let b = LinearWord::from_word(b).combine(&LinearWord::exact(*bound), false)?;
            if a.combine(&b, true)?.lower > 0 {
                return Err(LogicError::Unproved);
            }
            additions.push(Fact::Compare(
                left.ty,
                Comparison::LessEqual,
                Term::Word(a),
                Term::Word(b),
            ));
        }
        // Exact numeric duplicates are common when several leaves share a
        // historical source. Bounds are part of this key: never discard a
        // tighter or conflicting observation merely because its shape matches.
        let mut unique = Vec::new();
        for addition in additions {
            let mut repeated = false;
            if let Fact::Compare(t, op, Term::Word(a), Term::Word(b)) = &addition {
                for previous in self.facts.iter().chain(&unique) {
                    budget.charge(1)?;
                    if let Fact::Compare(u, prev_op, Term::Word(c), Term::Word(d)) = previous
                        && t == u
                        && op == prev_op
                        && a == c
                        && b == d
                    {
                        repeated = true;
                        break;
                    }
                }
            }
            if !repeated {
                unique.push(addition);
            }
        }
        Ok(unique)
    }

    /// Import one already established mathematical difference bound.
    #[cfg(test)]
    pub(crate) fn extend_difference(
        &mut self,
        left: &TypedLogicValue<T, A, R>,
        right: &TypedLogicValue<T, A, R>,
        bound: i128,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        self.extend_observations(&[], &[(left.clone(), right.clone(), bound)], budget)
    }

    /// Check the final domain of a mathematical template after substitution.
    /// Source DAG evaluation separately checks every arithmetic intermediate.
    pub(crate) fn check_word_domain(
        &self,
        ty: LogicType<T>,
        mut word: LinearWord<A>,
        budget: &mut LogicBudget,
    ) -> Result<AffineValue<A>, LogicError> {
        budget.charge(1 + word.terms.len())?;
        if !matches!(ty, LogicType::U64 | LogicType::Usize) {
            return Err(LogicError::TypeMismatch);
        }
        if word.terms.len() > MAX_LINEAR_TERMS {
            return Err(LogicError::Budget);
        }
        if word.lower > word.upper {
            return Err(LogicError::Unproved);
        }
        self.refine_word(ty, &mut word, budget)?;
        word.into_word()
    }

    /// Positive conjunctions contribute their individual premises; other
    /// available Boolean terms retain their complete structure. A missing leaf
    /// disables its dependent terms, never promotes an unknown disjunct.
    #[cfg(test)]
    pub(crate) fn extend(
        &mut self,
        expression: &LogicExpression<T>,
        leaves: &ExpressionLeaves<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        self.extend_batch(&[(expression, leaves)], budget)
    }

    /// Qualify a complete batch before publishing it. Checking consistency
    /// once avoids rebuilding every prefix of the same immutable premises.
    #[cfg(test)]
    pub(crate) fn extend_batch(
        &mut self,
        batch: &[ExpressionInput<'_, T, A, R>],
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        self.extend_inputs(&[], &[], batch, budget)
    }

    /// Publish actual observations and saved guarantees in one transaction.
    /// Both input families are premises established by the adapter; pending
    /// goals belong to `proves_batch` and must never enter this batch.
    pub(crate) fn extend_inputs(
        &mut self,
        booleans: &[(TypedLogicValue<T, A, R>, bool)],
        differences: &[DifferenceObservation<T, A, R>],
        batch: &[ExpressionInput<'_, T, A, R>],
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        budget.charge(batch.len())?;
        if batch.len() > MAX_CONSTRAINTS {
            return Err(LogicError::Budget);
        }
        let mut additions = self.observation_additions(booleans, differences, budget)?;
        for (expression, leaves) in batch {
            additions.extend(Self::constraint_additions(expression, leaves, budget)?);
        }
        if !additions.is_empty() {
            let mut prepared = self.constraint_graph(&additions, budget)?;
            prepared.propagate(budget)?;
            self.facts.extend(additions);
            self.prepared = prepared;
        }
        Ok(())
    }

    fn constraint_additions(
        expression: &LogicExpression<T>,
        leaves: &ExpressionLeaves<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<Fact<T, A, R>>, LogicError> {
        let values = Self::prepare(expression, leaves, true, budget)?;
        if expression.nodes[expression.root as usize].ty != LogicType::Bool {
            return Err(LogicError::TypeMismatch);
        }
        let clause = clause::Clause::new(expression, &values, budget)?;
        let mut pending = vec![expression.root];
        let mut visited = BTreeSet::new();
        let mut additions = Vec::new();
        while let Some(id) = pending.pop() {
            budget.charge(1)?;
            if !visited.insert(id) {
                continue;
            }
            let kind = &expression.nodes[id as usize].kind;
            let comparison = match *kind {
                LogicNodeKind::And(a, b) => {
                    pending.extend([a, b]);
                    continue;
                }
                LogicNodeKind::Equal(a, b) => Some((Comparison::Equal, a, b)),
                LogicNodeKind::Less(a, b) => Some((Comparison::Less, a, b)),
                LogicNodeKind::LessEqual(a, b) => Some((Comparison::LessEqual, a, b)),
                _ => None,
            };
            let mut retained = false;
            if let Some((op, a, b)) = comparison {
                if let (Some(a_value), Some(b_value)) = (&values[a as usize], &values[b as usize]) {
                    // Do not publish consequences of a demonstrably false
                    // imported premise, even when its original machine
                    // evaluation could not establish arithmetic definedness.
                    match (a_value, b_value) {
                        (Term::Word(a), Term::Word(b)) => {
                            for (a, b, strict) in directions(op, a, b) {
                                let difference = a
                                    .combine(b, true)?
                                    .combine(&LinearWord::exact(i128::from(strict)), false)?;
                                if difference.lower > 0 {
                                    return Err(LogicError::Unproved);
                                }
                            }
                        }
                        (Term::Bool(a), Term::Bool(b)) if a.bool_equal(b) == Some(false) => {
                            return Err(LogicError::Unproved);
                        }
                        _ => {}
                    }
                    retained = true;
                    additions.push(Fact::Compare(
                        expression.nodes[a as usize].ty,
                        op,
                        a_value.clone(),
                        b_value.clone(),
                    ));
                }
            } else if let Some(Term::Bool(value)) = &values[id as usize] {
                if value.known_boolean() == Some(false) {
                    return Err(LogicError::Unproved);
                }
                retained = true;
                additions.push(Fact::Boolean(value.clone(), true));
            }
            if !retained && clause.nodes[id as usize].is_some() {
                budget.charge(id as usize + 1)?;
                additions.push(Fact::Clause(clause::Clause {
                    nodes: clause.nodes[..=id as usize].to_vec(),
                    root: id,
                }));
            }
        }
        Ok(additions)
    }

    fn prepare(
        expression: &LogicExpression<T>,
        leaves: &ExpressionLeaves<T, A, R>,
        established_arithmetic: bool,
        budget: &mut LogicBudget,
    ) -> Result<Vec<Option<Term<A, R>>>, LogicError> {
        budget.charge(expression.nodes.len() + leaves.len())?;
        if expression.nodes.len() > MAX_EXPRESSION_NODES || leaves.len() > MAX_EXPRESSION_NODES {
            return Err(LogicError::Budget);
        }
        let mut resolved = BTreeMap::new();
        for (id, value) in leaves {
            let node = expression
                .nodes
                .get(*id as usize)
                .ok_or(LogicError::InvalidNode)?;
            if !matches!(
                node.kind,
                LogicNodeKind::Word(_)
                    | LogicNodeKind::Bool(_)
                    | LogicNodeKind::Binder(_)
                    | LogicNodeKind::Observe { .. }
                    | LogicNodeKind::Resource { .. }
            ) || resolved.insert(*id, value.as_ref()).is_some()
            {
                return Err(LogicError::InvalidNode);
            }
            if let Some(value) = value {
                if value.ty != node.ty {
                    return Err(LogicError::TypeMismatch);
                }
                validate_value(value, budget)?;
            }
        }

        // Validate the complete DAG with observations replaced by typed inputs.
        // Scope and memory admission remain the responsibility of the adapter.
        let mut normalized = expression.clone();
        let mut types = Vec::new();
        for (id, node) in normalized.nodes.iter_mut().enumerate() {
            if matches!(
                node.kind,
                LogicNodeKind::Binder(_)
                    | LogicNodeKind::Observe { .. }
                    | LogicNodeKind::Resource { .. }
            ) {
                if !resolved.contains_key(&(id as u32)) {
                    return Err(LogicError::Unbound);
                }
                node.kind = LogicNodeKind::Binder(LogicBinder::Parameter(types.len() as u32));
                types.push(node.ty);
            }
        }
        normalized.validate(&types, &[], &|_, _, _, _| None, &|_, _| None, budget)?;
        let mut values: Vec<Option<Term<A, R>>> = Vec::new();
        for (id, node) in expression.nodes.iter().enumerate() {
            budget.charge(1 + MAX_LINEAR_TERMS)?;
            let word = |id: u32| match &values[id as usize] {
                Some(Term::Word(w)) => Some(w),
                _ => None,
            };
            let value = match &node.kind {
                LogicNodeKind::Word(n) => Some(Term::Word(LinearWord::exact(i128::from(*n)))),
                LogicNodeKind::Bool(b) => Some(Term::Bool(LogicValue::Bool(Some(*b)))),
                LogicNodeKind::Binder(_)
                | LogicNodeKind::Observe { .. }
                | LogicNodeKind::Resource { .. } => {
                    match resolved
                        .get(&(id as u32))
                        .copied()
                        .flatten()
                        .map(|v| &v.value)
                    {
                        Some(LogicValue::Word(w)) => Some(Term::Word(LinearWord::from_word(w))),
                        Some(
                            v @ (LogicValue::Bool(_)
                            | LogicValue::BoolAtom { .. }
                            | LogicValue::BoolComparison { .. }
                            | LogicValue::BoolBinary { .. }),
                        ) => Some(Term::Bool(v.clone())),
                        _ => None,
                    }
                }
                LogicNodeKind::Add(a, b) | LogicNodeKind::Sub(a, b) if established_arithmetic => {
                    match (word(*a), word(*b)) {
                        (Some(a), Some(b)) => Some(Term::Word(
                            a.combine(b, matches!(node.kind, LogicNodeKind::Sub(..)))?,
                        )),
                        _ => None,
                    }
                }
                LogicNodeKind::Scale { operand, factor } if established_arithmetic => {
                    word(*operand)
                        .map(|w| w.scale(*factor).map(Term::Word))
                        .transpose()?
                }
                LogicNodeKind::Not(a) => match &values[*a as usize] {
                    Some(Term::Bool(value)) => Some(Term::Bool(value.bool_not())),
                    _ => None,
                },
                LogicNodeKind::And(a, b) | LogicNodeKind::Or(a, b) | LogicNodeKind::Equal(a, b) => {
                    match (&values[*a as usize], &values[*b as usize]) {
                        (Some(Term::Bool(a)), Some(Term::Bool(b))) => {
                            let op = match node.kind {
                                LogicNodeKind::And(..) => BooleanOperation::And,
                                LogicNodeKind::Or(..) => BooleanOperation::Or,
                                _ => BooleanOperation::Equal,
                            };
                            match LogicValue::boolean_binary(
                                op,
                                a.clone(),
                                b.clone(),
                                false,
                                budget,
                            ) {
                                Ok(value) => Some(Term::Bool(value)),
                                Err(LogicError::Unbound) => None,
                                Err(error) => return Err(error),
                            }
                        }
                        _ => None,
                    }
                }
                _ => None,
            };
            values.push(value);
        }
        Ok(values)
    }

    fn numeric_graph(
        &self,
        ty: LogicType<T>,
        budget: &mut LogicBudget,
    ) -> Result<linear::Graph<A>, LogicError> {
        let mut graph = self.constraint_graph(&[], budget)?;
        graph.propagate(budget)?;
        graph.numeric_graph(ty, budget)
    }

    fn refine_word(
        &self,
        ty: LogicType<T>,
        word: &mut LinearWord<A>,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        let mut graph = self.constraint_graph(&[], budget)?;
        graph.propagate(budget)?;
        graph.refine_word(ty, word, budget)
    }

    pub(crate) fn refine(
        &self,
        mut target: TypedLogicValue<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<TypedLogicValue<T, A, R>, LogicError> {
        budget.charge(1)?;
        validate_value(&target, budget)?;
        if let LogicValue::Word(word) = &mut target.value {
            let mut mathematical = LinearWord::from_word(word);
            self.refine_word(target.ty, &mut mathematical, budget)?;
            word.lower = u64::try_from(mathematical.lower).map_err(|_| LogicError::Unproved)?;
            word.upper = u64::try_from(mathematical.upper).map_err(|_| LogicError::Unproved)?;
            return Ok(target);
        }
        if target.ty == LogicType::Bool {
            let mut graph = self.constraint_graph(&[], budget)?;
            let literal = graph.insert(&target.value, budget)?;
            graph.propagate(budget)?;
            if let Some(truth) = graph.forced(literal, budget)? {
                set_bool(&mut target.value, truth)?;
            }
        }
        Ok(target)
    }

    pub(crate) fn entails(
        &self,
        comparison: Comparison,
        left: &TypedLogicValue<T, A, R>,
        right: &TypedLogicValue<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<bool, LogicError> {
        budget.charge(1 + MAX_LINEAR_TERMS)?;
        validate_value(left, budget)?;
        validate_value(right, budget)?;
        if left.ty != right.ty {
            return Err(LogicError::TypeMismatch);
        }
        let operand_type = left.ty;
        if let (LogicValue::Word(a), LogicValue::Word(b)) = (&left.value, &right.value) {
            let a = LinearWord::from_word(a);
            let b = LinearWord::from_word(b);
            return self
                .numeric_graph(operand_type, budget)?
                .entails(comparison, &a, &b, budget);
        }

        if comparison != Comparison::Equal || left.ty != LogicType::Bool {
            return Ok(false);
        }
        let mut graph = self.constraint_graph(&[], budget)?;
        let a = graph.insert(&left.value, budget)?;
        let b = graph.insert(&right.value, budget)?;
        let equality = graph.equal(a, b, budget)?;
        graph.propagate(budget)?;
        Ok(graph.forced(equality, budget)? == Some(true))
    }
}

fn validate_value<T, A: Ord, R>(
    value: &TypedLogicValue<T, A, R>,
    budget: &mut LogicBudget,
) -> Result<(), LogicError> {
    for leaf in value.value.capture_leaves(budget)? {
        let words = match leaf {
            LogicValue::Word(word) => vec![word],
            LogicValue::BoolComparison { left, right, .. } => vec![left, right],
            _ => vec![],
        };
        for word in words {
            budget.charge(word.terms.len())?;
            if word.lower > word.upper {
                return Err(LogicError::InvalidNode);
            }
            if word.terms.len() > MAX_LINEAR_TERMS {
                return Err(LogicError::Budget);
            }
        }
    }

    match (&value.ty, &value.value) {
        (LogicType::U64 | LogicType::Usize, LogicValue::Word(word)) => {
            if word.lower > word.upper {
                return Err(LogicError::InvalidNode);
            }
            if word.terms.len() > MAX_LINEAR_TERMS {
                return Err(LogicError::Budget);
            }
            Ok(())
        }
        (
            LogicType::Bool,
            LogicValue::Bool(_)
            | LogicValue::BoolAtom { .. }
            | LogicValue::BoolComparison { .. }
            | LogicValue::BoolBinary { .. },
        )
        | (LogicType::Resource(_), LogicValue::Resource(_) | LogicValue::ResourceAtom { .. }) => {
            Ok(())
        }
        _ => Err(LogicError::TypeMismatch),
    }
}

fn directions<'a, A: Ord>(
    op: Comparison,
    a: &'a LinearWord<A>,
    b: &'a LinearWord<A>,
) -> Vec<(&'a LinearWord<A>, &'a LinearWord<A>, bool)> {
    match op {
        Comparison::Equal => vec![(a, b, false), (b, a, false)],
        Comparison::Less => vec![(a, b, true)],
        Comparison::LessEqual => vec![(a, b, false)],
    }
}

fn set_bool<A: Ord + Clone, R: Clone>(
    value: &mut LogicValue<A, R>,
    known: bool,
) -> Result<(), LogicError> {
    if value
        .known_boolean()
        .is_some_and(|previous| previous != known)
    {
        return Err(LogicError::Unproved);
    }
    *value = LogicValue::Bool(Some(known));
    Ok(())
}

/// Project q * target + k <= 0 when every symbolic coefficient matches.
/// Equal intervals never establish symbolic identity.
fn project_bound<A: Ord + Clone>(
    target: &mut LinearWord<A>,
    bound: &LinearWord<A>,
) -> Result<(), LogicError> {
    let Some((atom, coefficient)) = target.terms.first_key_value() else {
        return Ok(());
    };
    let Some(n) = bound.terms.get(atom) else {
        return Ok(());
    };
    if n.checked_rem(*coefficient) != Some(0) {
        return Ok(());
    }
    let ratio = n.checked_div(*coefficient).ok_or(LogicError::Overflow)?;
    if ratio == 0 || bound.terms.len() != target.terms.len() {
        return Ok(());
    }
    for (atom, coefficient) in &target.terms {
        if bound.terms.get(atom).copied()
            != Some(coefficient.checked_mul(ratio).ok_or(LogicError::Overflow)?)
        {
            return Ok(());
        }
    }
    let rhs = target
        .constant
        .checked_mul(ratio)
        .and_then(|v| v.checked_sub(bound.constant))
        .ok_or(LogicError::Overflow)?;
    if ratio > 0 {
        let upper = rhs.div_euclid(ratio);
        target.upper = target.upper.min(upper);
    } else {
        let divisor = ratio.checked_neg().ok_or(LogicError::Overflow)?;
        let rhs = rhs.checked_neg().ok_or(LogicError::Overflow)?;
        let lower = rhs
            .div_euclid(divisor)
            .checked_add(i128::from(rhs.rem_euclid(divisor) != 0))
            .ok_or(LogicError::Overflow)?;
        target.lower = target.lower.max(lower);
    }
    if target.lower > target.upper {
        return Err(LogicError::Unproved);
    }
    Ok(())
}

#[cfg(test)]
mod tests;
