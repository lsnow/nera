//! Bounded truth propagation over already admitted immutable Boolean values.
//! Source discovery and resource authority remain outside this component.
use super::*;
use crate::predicate_logic::scalar_template::ScalarTemplate;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Literal {
    node: usize,
    negated: bool,
}

#[derive(Clone, PartialEq, Eq)]
enum Identity<A: Ord> {
    Leaf(ScalarTemplate<A>),
    Gate(BooleanOperation, Literal, Literal),
    Anonymous,
    External(usize),
}

#[derive(Clone)]
pub(super) struct BooleanGraph<A: Ord> {
    nodes: Vec<(Identity<A>, Option<bool>)>,
}

impl<A: Ord + Clone> BooleanGraph<A> {
    pub(super) fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    pub(super) fn clone_cost(&self) -> usize {
        self.nodes.len()
    }

    fn intern(
        &mut self,
        mut identity: Identity<A>,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        // All supported Boolean gates are commutative. This does not rewrite
        // arbitrary formulas, and never identifies two distinct leaf symbols.
        if let Identity::Gate(_, left, right) = &mut identity
            && *right < *left
        {
            std::mem::swap(left, right);
        }
        for (node, (previous, _)) in self.nodes.iter().enumerate() {
            budget.charge(1)?;
            let same = match (previous, &identity) {
                (
                    Identity::Leaf(ScalarTemplate::Comparison {
                        word_type: at,
                        comparison: WordComparison::Equal,
                        left: al,
                        right: ar,
                        negated: an,
                    }),
                    Identity::Leaf(ScalarTemplate::Comparison {
                        word_type: bt,
                        comparison: WordComparison::Equal,
                        left: bl,
                        right: br,
                        negated: bn,
                    }),
                ) => {
                    budget.charge(4 * MAX_LINEAR_TERMS)?;
                    at == bt && an == bn && (al == bl && ar == br || al == br && ar == bl)
                }
                _ => !matches!(identity, Identity::Anonymous) && *previous == identity,
            };
            if same {
                return Ok(Literal {
                    node,
                    negated: false,
                });
            }
        }
        budget.charge(1)?;
        if self.nodes.len() >= MAX_EXPRESSION_NODES {
            return Err(LogicError::Budget);
        }
        let node = self.nodes.len();
        self.nodes.push((identity, None));
        Ok(Literal {
            node,
            negated: false,
        })
    }

    pub(super) fn insert<R: Clone>(
        &mut self,
        value: &LogicValue<A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        value.capture_leaves(budget)?;
        self.insert_checked(value, budget)
    }

    fn insert_checked<R: Clone>(
        &mut self,
        value: &LogicValue<A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        budget.charge(1)?;
        let (identity, negated) = match value {
            LogicValue::BoolBinary {
                operation,
                left,
                right,
                negated,
            } => {
                let left = self.insert_checked(left, budget)?;
                let right = self.insert_checked(right, budget)?;
                (Identity::Gate(*operation, left, right), *negated)
            }
            LogicValue::Bool(None) => (Identity::Anonymous, false),
            LogicValue::Bool(_)
            | LogicValue::BoolAtom { .. }
            | LogicValue::BoolComparison { .. } => {
                let mut shape =
                    ScalarTemplate::capture(value, &mut |atom, _, _| Ok(atom.clone()), budget)?;
                let negated = match &mut shape {
                    ScalarTemplate::BoolAtom { negated, .. }
                    | ScalarTemplate::Comparison { negated, .. } => std::mem::take(negated),
                    _ => false,
                };
                (Identity::Leaf(shape), negated)
            }
            _ => return Err(LogicError::TypeMismatch),
        };
        let mut literal = self.intern(identity, budget)?;
        literal.negated = negated;
        if let Some(truth) = value.known_boolean() {
            self.assign(literal, truth)?;
        }
        Ok(literal)
    }

    pub(super) fn equal(
        &mut self,
        left: Literal,
        right: Literal,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        self.intern(Identity::Gate(BooleanOperation::Equal, left, right), budget)
    }

    pub(super) fn known(&self, literal: Literal) -> Option<bool> {
        self.nodes[literal.node].1.map(|v| v ^ literal.negated)
    }

    /// Query a propagated graph without assigning the proposed conclusion.
    /// Project only Boolean gates and admitted truths into the finite service;
    /// external numeric observations remain independent propositional inputs.
    pub(super) fn forced(
        &self,
        literal: Literal,
        budget: &mut LogicBudget,
    ) -> Result<Option<bool>, LogicError> {
        if let Some(value) = self.known(literal) {
            return Ok(Some(value));
        }
        Ok(self.forced_many(&[literal], budget)?[0])
    }

    pub(super) fn forced_many(
        &self,
        literals: &[Literal],
        budget: &mut LogicBudget,
    ) -> Result<Vec<Option<bool>>, LogicError> {
        self.forced_many_with_models(literals, &[], budget, &mut |_, _| Ok(true))
    }

    /// Project requested theory observations alongside queries without
    /// admitting either as an assignment. Theory policy remains with callers.
    pub(super) fn forced_many_with_models(
        &self,
        literals: &[Literal],
        observations: &[Literal],
        budget: &mut LogicBudget,
        admit: &mut impl FnMut(&[bool], &mut LogicBudget) -> Result<bool, LogicError>,
    ) -> Result<Vec<Option<bool>>, LogicError> {
        use crate::predicate_logic::propositional::{self, Literal as Input, Node};
        // Keep every admitted assignment and its dependencies, plus the
        // queried expressions. Unconstrained spectator nodes add no premise.
        let mut pending = literals
            .iter()
            .chain(observations)
            .map(|literal| literal.node)
            .collect::<Vec<_>>();
        for (id, (_, truth)) in self.nodes.iter().enumerate() {
            budget.charge(1)?;
            if truth.is_some() {
                pending.push(id);
            }
        }
        let mut relevant = BTreeSet::new();
        while let Some(id) = pending.pop() {
            budget.charge(1)?;
            let (identity, _) = self.nodes.get(id).ok_or(LogicError::InvalidNode)?;
            if !relevant.insert(id) {
                continue;
            }
            if let Identity::Gate(_, a, b) = identity {
                pending.extend([a.node, b.node]);
            }
        }
        let project = |literal: Literal, mapping: &[Option<usize>]| -> Result<Input, LogicError> {
            Ok(Input {
                node: mapping
                    .get(literal.node)
                    .copied()
                    .flatten()
                    .ok_or(LogicError::InvalidNode)?,
                negated: literal.negated,
            })
        };
        let mut nodes = Vec::new();
        let mut known = Vec::new();
        let mut mapping = vec![None; self.nodes.len()];
        for (id, (identity, truth)) in self.nodes.iter().enumerate() {
            budget.charge(1)?;
            if !relevant.contains(&id) {
                continue;
            }
            let node = match identity {
                Identity::Gate(operation, a, b) => {
                    Node::Gate(*operation, project(*a, &mapping)?, project(*b, &mapping)?)
                }
                Identity::Leaf(ScalarTemplate::Bool(value)) => Node::Constant(*value),
                _ => Node::Input(id),
            };
            mapping[id] = Some(nodes.len());
            nodes.push(node);
            known.push(*truth);
        }
        budget.charge(literals.len())?;
        let queries = literals
            .iter()
            .copied()
            .map(|literal| project(literal, &mapping))
            .collect::<Result<Vec<_>, _>>()?;
        budget.charge(observations.len())?;
        let observations = observations
            .iter()
            .copied()
            .map(|literal| project(literal, &mapping))
            .collect::<Result<Vec<_>, _>>()?;
        propositional::forced_many_with_models(
            &nodes,
            &known,
            &queries,
            &observations,
            budget,
            admit,
        )
    }

    /// An unknown primitive observation can be forced only through an admitted
    /// gate truth. Do not enumerate unrelated numeric queries or independent
    /// free observations merely because they occur in the same fact graph.
    pub(super) fn constrained_observations(
        &self,
        observations: &[Literal],
        budget: &mut LogicBudget,
    ) -> Result<Vec<Literal>, LogicError> {
        let mut pending = Vec::new();
        for (id, (identity, truth)) in self.nodes.iter().enumerate() {
            budget.charge(1)?;
            if truth.is_some() && matches!(identity, Identity::Gate(..)) {
                pending.push(id);
            }
        }
        let mut reached = BTreeSet::new();
        while let Some(id) = pending.pop() {
            budget.charge(1)?;
            if !reached.insert(id) {
                continue;
            }
            if let Identity::Gate(_, a, b) = self.nodes[id].0 {
                pending.extend([a.node, b.node]);
            }
        }
        let mut result = Vec::new();
        for literal in observations {
            budget.charge(1)?;
            if reached.contains(&literal.node) {
                result.push(*literal);
            }
        }
        Ok(result)
    }

    pub(super) fn assign(&mut self, literal: Literal, truth: bool) -> Result<bool, LogicError> {
        let truth = truth ^ literal.negated;
        let known = &mut self.nodes[literal.node].1;
        if known.is_some_and(|old| old != truth) {
            return Err(LogicError::Unproved);
        }
        let changed = known.is_none();
        *known = Some(truth);
        Ok(changed)
    }

    /// Filter each gate's four truth-table rows using known values and shared
    /// leaf identities. Commit only values common to every surviving row.
    /// Each round fixes at least one unknown or terminates; all work is charged.
    pub(super) fn propagate(&mut self, budget: &mut LogicBudget) -> Result<(), LogicError> {
        loop {
            let mut changed = false;
            for node in 0..self.nodes.len() {
                budget.charge(1)?;
                let Identity::Gate(operation, left, right) = self.nodes[node].0 else {
                    continue;
                };
                let literals = [
                    left,
                    right,
                    Literal {
                        node,
                        negated: false,
                    },
                ];
                let mut possibilities = [0u8; 3];
                for a in [false, true] {
                    for b in [false, true] {
                        budget.charge(1)?;
                        let row = [a, b, operation.evaluate(Some(a), Some(b)).unwrap()];
                        let consistent = (0..3).all(|i| {
                            self.known(literals[i]).is_none_or(|v| v == row[i])
                                && (0..i).all(|j| {
                                    literals[i].node != literals[j].node
                                        || (row[i] ^ literals[i].negated)
                                            == (row[j] ^ literals[j].negated)
                                })
                        });
                        if consistent {
                            for i in 0..3 {
                                possibilities[i] |= 1 << u8::from(row[i]);
                            }
                        }
                    }
                }
                if possibilities[0] == 0 {
                    return Err(LogicError::Unproved);
                }
                for i in 0..3 {
                    match possibilities[i] {
                        1 => changed |= self.assign(literals[i], false)?,
                        2 => changed |= self.assign(literals[i], true)?,
                        _ => {}
                    }
                }
            }
            if !changed {
                return Ok(());
            }
        }
    }
}

impl Literal {
    pub(super) fn not(self) -> Self {
        Self {
            negated: !self.negated,
            ..self
        }
    }
}
impl<A: Ord + Clone> BooleanGraph<A> {
    pub(super) fn external(
        &mut self,
        id: usize,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        self.intern(Identity::External(id), budget)
    }
    pub(super) fn gate(
        &mut self,
        op: BooleanOperation,
        a: Literal,
        b: Literal,
        budget: &mut LogicBudget,
    ) -> Result<Literal, LogicError> {
        self.intern(Identity::Gate(op, a, b), budget)
    }
}

#[cfg(test)]
mod tests;
