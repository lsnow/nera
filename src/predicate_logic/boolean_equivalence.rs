//! Propositional equivalence over qualified scalar shapes. Numeric comparisons
//! are independent typed atoms; captured truth/ranges are not assumptions.
//! This bounded decision procedure neither aligns sources nor rewrites captures.
use super::scalar_template::ScalarTemplate;
use super::*;

use super::propositional::{self, Literal, Node};

#[cfg(test)]
pub(super) fn equivalent_values<A: Ord + Clone, R: Clone>(
    left: &LogicValue<A, R>,
    right: &LogicValue<A, R>,
    budget: &mut LogicBudget,
) -> Result<bool, LogicError> {
    let shapes = [left, right]
        .into_iter()
        .map(|value| {
            let value = value.canonical_boolean_capture(budget)?;
            ScalarTemplate::capture(&value, &mut |atom, _, _| Ok(atom.clone()), budget)
        })
        .collect::<Result<Vec<_>, _>>();
    match shapes {
        Ok(shapes) => equivalent(&shapes[0], &shapes[1], budget),
        Err(LogicError::Unbound) => Ok(false),
        Err(error) => Err(error),
    }
}

/// Check every assignment or fail with Budget. No sampling, path truth or
/// selected satisfying branch may establish an expression identity.
pub(super) fn equivalent<A: Ord + Clone>(
    left: &ScalarTemplate<A>,
    right: &ScalarTemplate<A>,
    budget: &mut LogicBudget,
) -> Result<bool, LogicError> {
    let mut variables = BTreeMap::new();
    let mut nodes = Vec::new();
    let a = compile(left, &mut variables, &mut nodes, 0, budget)?;
    let b = compile(right, &mut variables, &mut nodes, 0, budget)?;
    let query = Literal::positive(nodes.len());
    nodes.push(Node::Gate(BooleanOperation::Equal, a, b));
    Ok(propositional::forced(&nodes, &vec![None; nodes.len()], query, budget)? == Some(true))
}

fn compile<A: Ord + Clone>(
    shape: &ScalarTemplate<A>,
    variables: &mut BTreeMap<ScalarTemplate<A>, usize>,
    nodes: &mut Vec<Node>,
    depth: usize,
    budget: &mut LogicBudget,
) -> Result<Literal, LogicError> {
    budget.charge(1)?;
    if depth >= MAX_EXPRESSION_DEPTH || nodes.len() >= 2 * MAX_EXPRESSION_NODES {
        return Err(LogicError::Budget);
    }
    let mut negation = false;
    let node = match shape {
        ScalarTemplate::Bool(value) => Node::Constant(*value),
        ScalarTemplate::BoolAtom { negated, .. } | ScalarTemplate::Comparison { negated, .. } => {
            let mut key = shape.clone();
            match &mut key {
                ScalarTemplate::BoolAtom { negated, .. }
                | ScalarTemplate::Comparison { negated, .. } => *negated = false,
                _ => unreachable!(),
            }
            let next = variables.len();
            negation = *negated;
            Node::Input(*variables.entry(key).or_insert(next))
        }
        ScalarTemplate::Boolean {
            operation,
            left,
            right,
            negated,
        } => {
            let a = compile(left, variables, nodes, depth + 1, budget)?;
            let b = compile(right, variables, nodes, depth + 1, budget)?;
            negation = *negated;
            Node::Gate(*operation, a, b)
        }
        ScalarTemplate::Word(_) => return Err(LogicError::TypeMismatch),
    };
    if nodes.len() >= 2 * MAX_EXPRESSION_NODES {
        return Err(LogicError::Budget);
    }
    let id = nodes.len();
    nodes.push(node);
    Ok(Literal {
        node: id,
        negated: negation,
    })
}
