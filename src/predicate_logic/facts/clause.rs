//! Typed Boolean structure over immutable scalar terms. Numeric propositions
//! remain typed mathematical comparisons; they are not runtime word values.
use super::*;

#[derive(Clone)]
pub(super) enum ClauseNode<T, A: Ord, R> {
    Value(LogicValue<A, R>),
    Numeric(LogicType<T>, Comparison, LinearWord<A>, LinearWord<A>),
    Not(u32),
    Binary(BooleanOperation, u32, u32),
}

#[derive(Clone)]
pub(super) struct Clause<T, A: Ord, R> {
    pub(super) nodes: Vec<Option<ClauseNode<T, A, R>>>,
    pub(super) root: u32,
}

impl<T: Copy + Eq, A: Ord + Clone, R: Clone> Clause<T, A, R> {
    /// Inputs have already passed DAG/type validation. Missing operands disable
    /// the dependent node, including annihilating Boolean operators.
    pub(super) fn new(
        expression: &LogicExpression<T>,
        values: &[Option<Term<A, R>>],
        budget: &mut LogicBudget,
    ) -> Result<Self, LogicError> {
        let mut nodes: Vec<Option<ClauseNode<T, A, R>>> = Vec::new();
        for (id, node) in expression.nodes.iter().enumerate() {
            budget.charge(1)?;
            let binary = |op, a: u32, b: u32| {
                (nodes[a as usize].is_some() && nodes[b as usize].is_some())
                    .then_some(ClauseNode::Binary(op, a, b))
            };
            let comparison = match node.kind {
                LogicNodeKind::Equal(a, b) => Some((Comparison::Equal, a, b)),
                LogicNodeKind::Less(a, b) => Some((Comparison::Less, a, b)),
                LogicNodeKind::LessEqual(a, b) => Some((Comparison::LessEqual, a, b)),
                _ => None,
            };
            let prepared = if let Some((op, a, b)) = comparison {
                match (&values[a as usize], &values[b as usize]) {
                    (Some(Term::Word(left)), Some(Term::Word(right))) => {
                        budget.charge(left.terms.len() + right.terms.len())?;
                        Some(ClauseNode::Numeric(
                            expression.nodes[a as usize].ty,
                            op,
                            left.clone(),
                            right.clone(),
                        ))
                    }
                    _ if expression.nodes[a as usize].ty == LogicType::Bool => {
                        binary(BooleanOperation::Equal, a, b)
                    }
                    _ => None,
                }
            } else {
                match node.kind {
                    LogicNodeKind::Not(a) => {
                        nodes[a as usize].is_some().then_some(ClauseNode::Not(a))
                    }
                    LogicNodeKind::And(a, b) => binary(BooleanOperation::And, a, b),
                    LogicNodeKind::Or(a, b) => binary(BooleanOperation::Or, a, b),
                    _ => match &values[id] {
                        Some(Term::Bool(value)) => Some(ClauseNode::Value(value.clone())),
                        _ => None,
                    },
                }
            };
            nodes.push(prepared);
        }
        Ok(Self {
            nodes,
            root: expression.root,
        })
    }
}
