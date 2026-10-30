//! Finite propositional queries over an immutable, topological graph.
//! Names, resources, numeric theories and premise admission belong to callers.
use super::{BooleanOperation, LogicBudget, LogicError, MAX_EXPRESSION_NODES};
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
pub(super) struct Literal {
    pub node: usize,
    pub negated: bool,
}

impl Literal {
    pub(super) fn positive(node: usize) -> Self {
        Self {
            node,
            negated: false,
        }
    }
    fn read(self, values: &[bool]) -> bool {
        values[self.node] ^ self.negated
    }
}

#[derive(Clone, Copy)]
pub(super) enum Node {
    Constant(bool),
    Input(usize),
    Gate(BooleanOperation, Literal, Literal),
}

/// Return only a value shared by every model of the admitted assignments.
/// Inconsistent premises are an error, never a vacuous proof. Budget covers
/// every possible row before enumeration; an incomplete search proves nothing.
pub(super) fn forced(
    nodes: &[Node],
    known: &[Option<bool>],
    query: Literal,
    budget: &mut LogicBudget,
) -> Result<Option<bool>, LogicError> {
    Ok(forced_many(nodes, known, &[query], budget)?[0])
}

/// All queries share one enumeration and one work charge. Neither the proposed
/// queries nor a particular model is admitted as a premise.
pub(super) fn forced_many(
    nodes: &[Node],
    known: &[Option<bool>],
    queries: &[Literal],
    budget: &mut LogicBudget,
) -> Result<Vec<Option<bool>>, LogicError> {
    forced_many_with_models(nodes, known, queries, &[], budget, &mut |_, _| Ok(true))
}

/// The caller may exclude a row only using independently established theory
/// inconsistency. Unknown rows must be admitted. The callback shares the query
/// budget, and any error discards the entire query's partial results.
pub(super) fn forced_many_with_models(
    nodes: &[Node],
    known: &[Option<bool>],
    queries: &[Literal],
    observations: &[Literal],
    budget: &mut LogicBudget,
    admit: &mut impl FnMut(&[bool], &mut LogicBudget) -> Result<bool, LogicError>,
) -> Result<Vec<Option<bool>>, LogicError> {
    if nodes.len() > 2 * MAX_EXPRESSION_NODES
        || queries.len() > MAX_EXPRESSION_NODES
        || observations.len() > MAX_EXPRESSION_NODES
    {
        return Err(LogicError::Budget);
    }
    if nodes.len() != known.len()
        || queries.is_empty()
        || queries
            .iter()
            .chain(observations)
            .any(|query| query.node >= nodes.len())
    {
        return Err(LogicError::InvalidNode);
    }
    budget.charge(queries.len() + observations.len())?;
    let mut inputs = BTreeMap::<usize, Option<bool>>::new();
    for (id, node) in nodes.iter().enumerate() {
        budget.charge(1)?;
        match *node {
            Node::Input(input) => {
                let value = inputs.entry(input).or_default();
                if let Some(truth) = known[id] {
                    if value.is_some_and(|old| old != truth) {
                        return Err(LogicError::Unproved);
                    }
                    *value = Some(truth);
                }
            }
            Node::Gate(_, a, b) if a.node >= id || b.node >= id => {
                return Err(LogicError::InvalidNode);
            }
            _ => {}
        }
    }
    let mut free = 0usize;
    let inputs = inputs
        .into_iter()
        .map(|(id, known)| {
            let bit = known.is_none().then(|| {
                let bit = free;
                free += 1;
                bit
            });
            (id, (known, bit))
        })
        .collect::<BTreeMap<_, _>>();
    let rows = 1usize
        .checked_shl(free.try_into().map_err(|_| LogicError::Budget)?)
        .ok_or(LogicError::Budget)?;
    budget.charge(
        rows.checked_mul(nodes.len() + 2 * queries.len() + observations.len())
            .ok_or(LogicError::Budget)?,
    )?;
    // Resolve input lookup once, outside the charged per-row linear traversal.
    let bindings = nodes
        .iter()
        .map(|node| match node {
            Node::Input(id) => Some(inputs[id]),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut values = vec![false; nodes.len()];
    let mut possibilities = vec![0u8; queries.len()];
    let mut observed = vec![false; observations.len()];
    for row in 0..rows {
        let mut admitted = true;
        for (id, node) in nodes.iter().enumerate() {
            values[id] = match *node {
                Node::Constant(value) => value,
                Node::Input(_) => {
                    let (value, bit) = bindings[id].ok_or(LogicError::InvalidNode)?;
                    match (value, bit) {
                        (Some(value), _) => value,
                        (None, Some(bit)) => row & (1usize << bit) != 0,
                        _ => return Err(LogicError::InvalidNode),
                    }
                }
                Node::Gate(operation, a, b) => match operation {
                    BooleanOperation::And => a.read(&values) && b.read(&values),
                    BooleanOperation::Or => a.read(&values) || b.read(&values),
                    BooleanOperation::Equal => a.read(&values) == b.read(&values),
                },
            };
            if known[id].is_some_and(|truth| truth != values[id]) {
                admitted = false;
                break;
            }
        }
        if admitted {
            for (value, observation) in observed.iter_mut().zip(observations) {
                *value = observation.read(&values);
            }
            if !admit(&observed, budget)? {
                continue;
            }
            for (possibility, query) in possibilities.iter_mut().zip(queries) {
                *possibility |= 1 << u8::from(query.read(&values));
            }
            if possibilities.iter().all(|value| *value == 3) {
                return Ok(vec![None; queries.len()]);
            }
        }
    }
    possibilities
        .into_iter()
        .map(|value| match value {
            0 => Err(LogicError::Unproved),
            1 => Ok(Some(false)),
            2 => Ok(Some(true)),
            _ => Ok(None),
        })
        .collect()
}

#[cfg(test)]
mod tests;
