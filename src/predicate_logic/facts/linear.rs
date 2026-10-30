//! Difference constraints over immutable affine expressions, not SSA IDs.
//! An edge u -> v with weight k means v <= u + k. Search never installs
//! premises in the resource state, and a negative cycle is an error.
use super::*;

const MAX_VERTICES: usize = MAX_EXPRESSION_NODES;
const MAX_EDGES: usize = MAX_SUBSTITUTION_NODES;

#[derive(Clone)]
pub(super) struct Graph<A: Ord> {
    vertices: BTreeMap<BTreeMap<A, i128>, usize>,
    edges: BTreeMap<(usize, usize), i128>,
    // Query-local paths, valid only while this exact graph is unchanged.
    // No resource or declaration identity enters this cache.
    distances: BTreeMap<Option<usize>, Vec<Option<i128>>>,
}

impl<A: Ord + Clone> Graph<A> {
    pub(super) fn new() -> Self {
        Self {
            vertices: BTreeMap::from([(BTreeMap::new(), 0)]),
            edges: BTreeMap::new(),
            distances: BTreeMap::new(),
        }
    }

    pub(super) fn clone_cost(&self) -> usize {
        self.vertices
            .keys()
            .map(|terms| 1 + terms.len())
            .sum::<usize>()
            + self.edges.len()
            + self.distances.values().map(Vec::len).sum::<usize>()
    }

    fn vertex(
        &mut self,
        terms: &BTreeMap<A, i128>,
        budget: &mut LogicBudget,
    ) -> Result<usize, LogicError> {
        budget.charge(1 + terms.len())?;
        if let Some(id) = self.vertices.get(terms) {
            return Ok(*id);
        }
        if terms.len() > MAX_LINEAR_TERMS || self.vertices.len() >= MAX_VERTICES {
            return Err(LogicError::Budget);
        }
        let id = self.vertices.len();
        self.vertices.insert(terms.clone(), id);
        self.distances.clear();
        Ok(id)
    }

    fn edge(
        &mut self,
        from: usize,
        to: usize,
        weight: i128,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        budget.charge(1)?;
        if let Some(old) = self.edges.get_mut(&(from, to)) {
            if weight < *old {
                *old = weight;
                self.distances.clear();
            }
        } else {
            if self.edges.len() >= MAX_EDGES {
                return Err(LogicError::Budget);
            }
            self.edges.insert((from, to), weight);
            self.distances.clear();
        }
        Ok(())
    }

    fn signed_vertices(
        &mut self,
        terms: &BTreeMap<A, i128>,
        budget: &mut LogicBudget,
    ) -> Result<(usize, usize), LogicError> {
        let mut positive = BTreeMap::new();
        let mut negative = BTreeMap::new();
        for (atom, coefficient) in terms {
            if *coefficient > 0 {
                positive.insert(atom.clone(), *coefficient);
            } else {
                negative.insert(
                    atom.clone(),
                    coefficient.checked_neg().ok_or(LogicError::Overflow)?,
                );
            }
        }
        Ok((
            self.vertex(&positive, budget)?,
            self.vertex(&negative, budget)?,
        ))
    }

    pub(super) fn word(
        &mut self,
        word: &LinearWord<A>,
        budget: &mut LogicBudget,
    ) -> Result<usize, LogicError> {
        let id = self.vertex(&word.terms, budget)?;
        self.edge(
            0,
            id,
            word.upper
                .checked_sub(word.constant)
                .ok_or(LogicError::Overflow)?,
            budget,
        )?;
        self.edge(
            id,
            0,
            word.constant
                .checked_sub(word.lower)
                .ok_or(LogicError::Overflow)?,
            budget,
        )?;
        Ok(id)
    }

    pub(super) fn comparison(
        &mut self,
        op: Comparison,
        a: &LinearWord<A>,
        b: &LinearWord<A>,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        let a_id = self.word(a, budget)?;
        let b_id = self.word(b, budget)?;
        for (index, (a, b, strict)) in directions(op, a, b).into_iter().enumerate() {
            let weight = b
                .constant
                .checked_sub(a.constant)
                .and_then(|k| k.checked_sub(i128::from(strict)))
                .ok_or(LogicError::Overflow)?;
            let (from, to) = if index == 0 {
                (b_id, a_id)
            } else {
                (a_id, b_id)
            };
            self.edge(from, to, weight, budget)?;
            // Also cancel common coefficients, allowing x + z <= y + z to
            // participate in the same graph as x <= y. Signed terms are split
            // algebraically; this makes no machine-arithmetic claim.
            let difference = a.combine(b, true)?;
            let (to, from) = self.signed_vertices(&difference.terms, budget)?;
            self.edge(from, to, weight, budget)?;
        }
        Ok(())
    }

    /// Synchronous relaxation avoids iteration-order-dependent deductions.
    /// With None, every vertex starts at zero to detect contradictions even
    /// in components not connected to a particular query.
    fn distances(
        &mut self,
        source: Option<usize>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<Option<i128>>, LogicError> {
        budget.charge(self.vertices.len())?;
        if let Some(saved) = self.distances.get(&source) {
            return Ok(saved.clone());
        }
        let mut distances: Vec<Option<i128>> = vec![None; self.vertices.len()];
        if let Some(source) = source {
            distances[source] = Some(0);
        } else {
            distances.fill(Some(0));
        }
        for round in 0..self.vertices.len() {
            budget.charge(distances.len())?;
            let mut next = distances.clone();
            let mut changed = false;
            for ((from, to), weight) in &self.edges {
                budget.charge(1)?;
                let Some(value) = distances[*from] else {
                    continue;
                };
                let candidate = value.checked_add(*weight).ok_or(LogicError::Overflow)?;
                if next[*to].is_none_or(|old| candidate < old) {
                    next[*to] = Some(candidate);
                    changed = true;
                }
            }
            if !changed {
                self.distances.insert(source, distances.clone());
                return Ok(distances);
            }
            if round + 1 == self.vertices.len() {
                return Err(LogicError::Unproved);
            }
            distances = next;
        }
        Err(LogicError::Unproved)
    }

    pub(super) fn consistent(&mut self, budget: &mut LogicBudget) -> Result<(), LogicError> {
        self.distances(None, budget).map(|_| ())
    }

    pub(super) fn entails(
        &mut self,
        op: Comparison,
        a: &LinearWord<A>,
        b: &LinearWord<A>,
        budget: &mut LogicBudget,
    ) -> Result<bool, LogicError> {
        let a_id = self.word(a, budget)?;
        let b_id = self.word(b, budget)?;
        // Register cancelled query vertices without adding the query as an edge.
        let mut goals = Vec::new();
        for (a, b, strict) in directions(op, a, b) {
            let difference = a.combine(b, true)?;
            let (to, from) = self.signed_vertices(&difference.terms, budget)?;
            let bound = difference
                .constant
                .checked_neg()
                .and_then(|v| v.checked_sub(i128::from(strict)))
                .ok_or(LogicError::Overflow)?;
            goals.push((from, to, bound));
        }
        self.consistent(budget)?;
        for (index, (from, to, bound)) in goals.into_iter().enumerate() {
            let distances = self.distances(Some(from), budget)?;
            if distances[to].is_some_and(|value| value <= bound) {
                continue;
            }
            let (from, to) = if index == 0 {
                (b_id, a_id)
            } else {
                (a_id, b_id)
            };
            if !self.distances(Some(from), budget)?[to].is_some_and(|value| value <= bound) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(super) fn bounds(
        &mut self,
        word: &LinearWord<A>,
        budget: &mut LogicBudget,
    ) -> Result<(i128, i128), LogicError> {
        let id = self.word(word, budget)?;
        // A signed affine query P - N + c need not occur verbatim in a
        // premise. Paths N -> P bound it above; paths P -> N bound it below.
        // Register only vertices, never assume the query is machine-defined.
        let (positive, negative) = self.signed_vertices(&word.terms, budget)?;
        self.consistent(budget)?;
        let mut upper = self.distances(Some(0), budget)?[id]
            .ok_or(LogicError::Unproved)?
            .checked_add(word.constant)
            .ok_or(LogicError::Overflow)?;
        let mut lower = word
            .constant
            .checked_sub(self.distances(Some(id), budget)?[0].ok_or(LogicError::Unproved)?)
            .ok_or(LogicError::Overflow)?;
        if (negative, positive) != (0, id) {
            if let Some(bound) = self.distances(Some(negative), budget)?[positive] {
                upper = upper.min(
                    word.constant
                        .checked_add(bound)
                        .ok_or(LogicError::Overflow)?,
                );
            }
            if let Some(bound) = self.distances(Some(positive), budget)?[negative] {
                lower = lower.max(
                    word.constant
                        .checked_sub(bound)
                        .ok_or(LogicError::Overflow)?,
                );
            }
        }
        if lower > upper {
            return Err(LogicError::Unproved);
        }
        Ok((lower, upper))
    }
}

#[cfg(test)]
mod tests;
