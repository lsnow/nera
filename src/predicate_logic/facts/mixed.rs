//! Bounded communication between the independent Boolean and difference domains.
//! Only forced propositions cross the boundary. A separate model adapter may
//! exclude Boolean rows contradicted by typed difference constraints; no chosen
//! row or temporary numeric premise is published as an established fact.
//! No permission or runtime source discovery is performed here.
use super::boolean::{BooleanGraph, Literal};
use super::clause::{Clause, ClauseNode};
use super::*;

mod models;

#[derive(Clone)]
struct Numeric<T, A: Ord> {
    ty: LogicType<T>,
    op: Comparison,
    left: LinearWord<A>,
    right: LinearWord<A>,
}

impl<T, A: Ord + Clone> Numeric<T, A> {
    fn known(&self) -> Result<Option<bool>, LogicError> {
        let difference = self.left.combine(&self.right, true)?;
        Ok(match self.op {
            Comparison::Equal if difference.lower == 0 && difference.upper == 0 => Some(true),
            Comparison::Equal if difference.upper < 0 || difference.lower > 0 => Some(false),
            Comparison::Less if difference.upper < 0 => Some(true),
            Comparison::Less if difference.lower >= 0 => Some(false),
            Comparison::LessEqual if difference.upper <= 0 => Some(true),
            Comparison::LessEqual if difference.lower > 0 => Some(false),
            _ => None,
        })
    }
}

#[derive(Clone)]
pub(super) struct MixedGraph<T, A: Ord> {
    booleans: BooleanGraph<A>,
    premises: Vec<Numeric<T, A>>,
    observations: Vec<(Numeric<T, A>, Literal)>,
    settled: bool,
    numeric: Vec<(LogicType<T>, linear::Graph<A>)>,
}

impl<T: Copy + Eq, A: Ord + Clone> MixedGraph<T, A> {
    pub(super) fn new() -> Self {
        Self {
            booleans: BooleanGraph::new(),
            premises: Vec::new(),
            observations: Vec::new(),
            settled: true,
            numeric: Vec::new(),
        }
    }

    pub(super) fn insert<R: Clone>(
        &mut self,
        value: &LogicValue<A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        self.settled = false;
        value.capture_leaves(budget)?;
        self.insert_capture(value, budget)
    }

    fn insert_capture<R: Clone>(
        &mut self,
        value: &LogicValue<A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        budget.charge(1)?;
        match value {
            LogicValue::BoolComparison {
                word_type,
                comparison,
                left,
                right,
                negated,
            } => {
                let literal = self.observe(
                    Numeric {
                        ty: word_type.logic_type(),
                        op: match comparison {
                            WordComparison::Equal => Comparison::Equal,
                            WordComparison::LessEqual => Comparison::LessEqual,
                        },
                        left: LinearWord::from_word(left),
                        right: LinearWord::from_word(right),
                    },
                    budget,
                )?;
                Ok(if *negated { literal.not() } else { literal })
            }
            LogicValue::BoolBinary {
                operation,
                left,
                right,
                negated,
            } => {
                let left = self.insert_capture(left, budget)?;
                let right = self.insert_capture(right, budget)?;
                let literal = self.booleans.gate(*operation, left, right, budget)?;
                Ok(if *negated { literal.not() } else { literal })
            }
            _ => self.booleans.insert(value, budget),
        }
    }
    pub(super) fn equal(
        &mut self,
        a: Literal,
        b: Literal,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        self.settled = false;
        self.booleans.equal(a, b, budget)
    }
    pub(super) fn known(&self, literal: Literal) -> Option<bool> {
        self.booleans.known(literal)
    }
    pub(super) fn forced(
        &self,
        literal: Literal,
        budget: &mut LogicBudget,
    ) -> Result<Option<bool>, LogicError> {
        if let Some(value) = self.known(literal) {
            return Ok(Some(value));
        }
        Ok(self.theory_forced(&[literal], budget)?[0])
    }

    fn observe(
        &mut self,
        numeric: Numeric<T, A>,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        self.settled = false;
        budget.charge(1 + numeric.left.terms.len() + numeric.right.terms.len())?;
        let known = numeric.known()?;
        for (old, literal) in &mut self.observations {
            budget.charge(1 + 2 * (numeric.left.terms.len() + numeric.right.terms.len()))?;
            let same = |a: &LinearWord<A>, b: &LinearWord<A>| {
                a.constant == b.constant && a.terms == b.terms
            };
            let direct = same(&old.left, &numeric.left) && same(&old.right, &numeric.right);
            let reversed = numeric.op == Comparison::Equal
                && same(&old.left, &numeric.right)
                && same(&old.right, &numeric.left);
            if old.ty == numeric.ty && old.op == numeric.op && (direct || reversed) {
                // Equality is symmetric even when false: its negation cannot
                // be recovered by choosing a direction in the numeric domain.
                let (left, right) = if direct {
                    (&numeric.left, &numeric.right)
                } else {
                    (&numeric.right, &numeric.left)
                };
                for (old, new) in [(&mut old.left, left), (&mut old.right, right)] {
                    old.lower = old.lower.max(new.lower);
                    old.upper = old.upper.min(new.upper);
                    if old.lower > old.upper {
                        return Err(LogicError::Unproved);
                    }
                }
                if let Some(truth) = known {
                    self.booleans.assign(*literal, truth)?;
                }
                return Ok(*literal);
            }
        }
        if self.observations.len() >= MAX_EXPRESSION_NODES {
            return Err(LogicError::Budget);
        }
        let literal = self.booleans.external(self.observations.len(), budget)?;
        self.observations.push((numeric, literal));
        // Keep the operand domains in observations even for a constant truth:
        // numeric_graph must still reject inconsistent copies of the same atom.
        if let Some(truth) = known {
            self.booleans.assign(literal, truth)?;
        }
        Ok(literal)
    }

    pub(super) fn insert_clause<R: Clone>(
        &mut self,
        clause: &Clause<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Option<Literal>, LogicError> {
        self.settled = false;
        let mut literals: Vec<Option<Literal>> = Vec::new();
        for node in &clause.nodes {
            budget.charge(1)?;
            let literal = match node {
                Some(ClauseNode::Value(value)) => Some(self.insert(value, budget)?),
                Some(ClauseNode::Numeric(ty, op, left, right)) => Some(self.observe(
                    Numeric {
                        ty: *ty,
                        op: *op,
                        left: left.clone(),
                        right: right.clone(),
                    },
                    budget,
                )?),
                Some(ClauseNode::Not(a)) => literals[*a as usize].map(Literal::not),
                Some(ClauseNode::Binary(op, a, b)) => {
                    match (literals[*a as usize], literals[*b as usize]) {
                        (Some(a), Some(b)) => Some(self.booleans.gate(*op, a, b, budget)?),
                        _ => None,
                    }
                }
                None => None,
            };
            literals.push(literal);
        }
        Ok(literals[clause.root as usize])
    }

    /// False equality is a disjunction, so it never becomes a convex numeric
    /// premise. Negated orders, in contrast, have an exact opposite order.
    fn consequence(n: &Numeric<T, A>, truth: bool) -> Option<Numeric<T, A>> {
        if truth {
            return Some(n.clone());
        }
        let op = match n.op {
            Comparison::Equal => return None,
            Comparison::Less => Comparison::LessEqual,
            Comparison::LessEqual => Comparison::Less,
        };
        Some(Numeric {
            ty: n.ty,
            op,
            left: n.right.clone(),
            right: n.left.clone(),
        })
    }

    pub(super) fn numeric_premises(
        &self,
        ty: LogicType<T>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<NumericPremise<A>>, LogicError> {
        let mut result = Vec::new();
        for n in &self.premises {
            budget.charge(1)?;
            if n.ty == ty {
                result.push((n.op, n.left.clone(), n.right.clone()));
            }
        }
        for (n, literal) in &self.observations {
            budget.charge(1)?;
            if n.ty == ty
                && let Some(n) = self
                    .known(*literal)
                    .and_then(|truth| Self::consequence(n, truth))
            {
                result.push((n.op, n.left, n.right));
            }
        }
        Ok(result)
    }

    pub(super) fn numeric_graph(
        &self,
        ty: LogicType<T>,
        budget: &mut LogicBudget,
    ) -> Result<linear::Graph<A>, LogicError> {
        if self.settled {
            if let Some((_, graph)) = self.numeric.iter().find(|(t, _)| *t == ty) {
                budget.charge(graph.clone_cost())?;
                return Ok(graph.clone());
            }
            budget.charge(1)?;
            return Ok(linear::Graph::new());
        }
        let mut graph = linear::Graph::new();
        for (op, left, right) in self.numeric_premises(ty, budget)? {
            graph.comparison(op, &left, &right, budget)?;
        }
        for (n, _) in &self.observations {
            budget.charge(1)?;
            if n.ty == ty {
                graph.word(&n.left, budget)?;
                graph.word(&n.right, budget)?;
            }
        }
        Ok(graph)
    }

    pub(super) fn word_facts(
        &self,
        ty: LogicType<T>,
        budget: &mut LogicBudget,
    ) -> Result<WordFacts<A>, LogicError> {
        Ok(WordFacts {
            premises: self.numeric_premises(ty, budget)?,
            graph: self.numeric_graph(ty, budget)?,
        })
    }

    pub(super) fn refine_word(
        &self,
        ty: LogicType<T>,
        word: &mut LinearWord<A>,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        self.word_facts(ty, budget)?.refine(word, budget)
    }

    pub(super) fn propagate(&mut self, budget: &mut LogicBudget) -> Result<(), LogicError> {
        budget.charge(1)?;
        if self.settled {
            return Ok(());
        }
        loop {
            self.booleans.propagate(budget)?;
            let mut numeric = Vec::new();
            // The two machine word types have separate graphs, even if a caller
            // happens to reuse an atom identifier across different typed inputs.
            for ty in [LogicType::U64, LogicType::Usize] {
                if !self.observations.iter().any(|(n, _)| n.ty == ty)
                    && !self.premises.iter().any(|n| n.ty == ty)
                {
                    continue;
                }
                let mut graph = self.numeric_graph(ty, budget)?;
                // Numeric-only batches must be consistent too, including
                // disconnected components with no Boolean observation/query.
                graph.consistent(budget)?;
                for (n, literal) in &self.observations {
                    budget.charge(1)?;
                    if n.ty != ty {
                        continue;
                    }
                    // These forced propositions already entered numeric_graph
                    // as premises; consistency above validates them together.
                    // False equality is disjunctive and must still be checked.
                    if self
                        .known(*literal)
                        .is_some_and(|truth| truth || n.op != Comparison::Equal)
                    {
                        continue;
                    }
                    let truth = if graph.entails(n.op, &n.left, &n.right, budget)? {
                        Some(true)
                    } else {
                        let opposite = match n.op {
                            Comparison::Less => {
                                graph.entails(Comparison::LessEqual, &n.right, &n.left, budget)?
                            }
                            Comparison::LessEqual => {
                                graph.entails(Comparison::Less, &n.right, &n.left, budget)?
                            }
                            Comparison::Equal => {
                                graph.entails(Comparison::Less, &n.left, &n.right, budget)?
                                    || graph.entails(Comparison::Less, &n.right, &n.left, budget)?
                            }
                        };
                        opposite.then_some(false)
                    };
                    if let Some(truth) = truth {
                        self.booleans.assign(*literal, truth)?;
                    }
                }
                numeric.push((ty, graph));
            }
            // Numeric consequences add no information to the numeric domain
            // that just derived them. Repeat that domain only if Boolean
            // propagation forces an additional numeric proposition. Still
            // propagate every Boolean gate to detect contradictions.
            budget.charge(self.observations.len())?;
            let before = self
                .observations
                .iter()
                .map(|(_, literal)| self.known(*literal))
                .collect::<Vec<_>>();
            self.booleans.propagate(budget)?;
            let promoted = self.promote_forced_numeric(budget)?;
            if !promoted
                && self
                    .observations
                    .iter()
                    .zip(before)
                    .all(|((_, literal), before)| self.known(*literal) == before)
            {
                self.numeric = numeric;
                self.settled = true;
                return Ok(());
            }
        }
    }

    /// At the local propagation fixed point, transfer only propositions shared
    /// by every Boolean model. One immutable batch shares the enumeration;
    /// numeric consequences are consumed by the existing typed graphs next
    /// round. Each successful round fixes at least one previously unknown node.
    fn promote_forced_numeric(&mut self, budget: &mut LogicBudget) -> Result<bool, LogicError> {
        let mut pending = Vec::new();
        for (_, literal) in &self.observations {
            budget.charge(1)?;
            if self.booleans.known(*literal).is_none() {
                pending.push(*literal);
            }
        }
        if pending.is_empty() {
            return Ok(false);
        }
        let pending = self.booleans.constrained_observations(&pending, budget)?;
        if pending.is_empty() {
            return Ok(false);
        }
        let values = self.booleans.forced_many(&pending, budget)?;
        let mut changed = false;
        for (literal, value) in pending.into_iter().zip(values) {
            budget.charge(1)?;
            if let Some(value) = value {
                changed |= self.booleans.assign(literal, value)?;
            }
        }
        Ok(changed)
    }
}

impl<T: Copy + Eq, A: Ord + Clone, R: Clone + Eq> EstablishedFacts<T, A, R> {
    pub(super) fn constraint_graph(
        &self,
        additions: &[Fact<T, A, R>],
        budget: &mut LogicBudget,
    ) -> Result<MixedGraph<T, A>, LogicError> {
        // Cloning copies the prepared domains and Boolean fixed point, never
        // a query's proposed truth. Charge the actual bounded catalog size.
        budget.charge(self.prepared.booleans.clone_cost())?;
        for n in self
            .prepared
            .premises
            .iter()
            .chain(self.prepared.observations.iter().map(|(n, _)| n))
        {
            budget.charge(1 + n.left.terms.len() + n.right.terms.len())?;
        }
        for (_, graph) in &self.prepared.numeric {
            budget.charge(graph.clone_cost())?;
        }
        let mut graph = self.prepared.clone();
        if !additions.is_empty() {
            graph.settled = false;
        }
        for fact in additions {
            budget.charge(1)?;
            match fact {
                Fact::Boolean(value, truth) => {
                    let literal = graph.insert(value, budget)?;
                    graph.booleans.assign(literal, *truth)?;
                }
                Fact::Compare(LogicType::Bool, Comparison::Equal, Term::Bool(a), Term::Bool(b)) => {
                    let a = graph.insert(a, budget)?;
                    let b = graph.insert(b, budget)?;
                    let equality = graph.equal(a, b, budget)?;
                    graph.booleans.assign(equality, true)?;
                }
                Fact::Compare(ty, op, Term::Word(left), Term::Word(right)) => {
                    graph.premises.push(Numeric {
                        ty: *ty,
                        op: *op,
                        left: left.clone(),
                        right: right.clone(),
                    });
                }
                Fact::Clause(clause) => {
                    if let Some(literal) = graph.insert_clause(clause, budget)? {
                        graph.booleans.assign(literal, true)?;
                    }
                }
                _ => {}
            }
        }
        Ok(graph)
    }
}

/// One typed numeric context for a checked expression. Only established
/// premises and validated operand bounds enter the graph; query operations
/// never become premises. The context is discarded at the query boundary.
pub(super) struct WordFacts<A: Ord> {
    premises: Vec<NumericPremise<A>>,
    graph: linear::Graph<A>,
}

impl<A: Ord + Clone> WordFacts<A> {
    pub(super) fn observe(
        &mut self,
        word: &LinearWord<A>,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        self.graph.word(word, budget).map(|_| ())
    }

    pub(super) fn consistent(&mut self, budget: &mut LogicBudget) -> Result<(), LogicError> {
        self.graph.consistent(budget)
    }

    pub(super) fn refine(
        &mut self,
        word: &mut LinearWord<A>,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        for (op, a, b) in &self.premises {
            budget.charge(1 + MAX_LINEAR_TERMS)?;
            for (left, right, strict) in directions(*op, a, b) {
                let strict = i128::from(strict);
                let upper = right
                    .upper
                    .checked_sub(strict)
                    .ok_or(LogicError::Overflow)?;
                project_bound(word, &left.combine(&LinearWord::exact(upper), true)?)?;
                let lower = left.lower.checked_add(strict).ok_or(LogicError::Overflow)?;
                project_bound(word, &LinearWord::exact(lower).combine(right, true)?)?;
                project_bound(
                    word,
                    &left
                        .combine(right, true)?
                        .combine(&LinearWord::exact(strict), false)?,
                )?;
            }
        }
        (word.lower, word.upper) = self.graph.bounds(word, budget)?;
        Ok(())
    }
}
