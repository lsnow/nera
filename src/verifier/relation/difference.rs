//! Bounded mathematical-integer difference queries over typed machine words.
//!
//! Inputs are premises, NOT trusted compiler facts. Only the local adapter may
//! obtain them from a ResourceState. This module cannot mutate resource state.
use std::collections::BTreeMap;

use super::{RelationComparison, RelationTerm};
use crate::{ObligationStatus, U64Interval, VirType, VirValueId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DifferenceLimits {
    pub max_variables: usize,
    pub max_constraints: usize,
    pub max_steps: usize,
    pub max_derivations: usize,
    pub max_branches: usize,
}

impl Default for DifferenceLimits {
    fn default() -> Self {
        Self {
            max_variables: 24,
            max_constraints: 128,
            max_steps: 65_536,
            max_derivations: 2_048,
            max_branches: 4,
        }
    }
}

/// The source of these premises is recorded by the enclosing CFG observation.
/// A Bound is `left - right <= bound`; EqualOffset is mathematical equality,
/// and must never be constructed from an unproved wrapping operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DifferencePremise {
    Interval {
        value: VirValueId,
        interval: U64Interval,
    },
    Bound {
        left: RelationTerm,
        right: RelationTerm,
        bound: i128,
    },
    EqualOffset {
        left: RelationTerm,
        right: RelationTerm,
        offset: i128,
    },
    Compare {
        comparison: RelationComparison,
        left: RelationTerm,
        right: RelationTerm,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DifferenceGoal {
    pub comparison: RelationComparison,
    pub left: RelationTerm,
    pub right: RelationTerm,
}

/// Edge ordinals refer to normalized edges in the corresponding branch.
/// Composition references strictly earlier nodes, never a pending invariant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DifferenceDerivation {
    Edge {
        left: usize,
        right: usize,
        bound: i128,
        premise: Option<usize>,
    },
    Compose {
        first: usize,
        second: usize,
        bound: i128,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DifferenceBranch {
    /// Each entry selects `<` or `>` for an original disequality, in order.
    pub choices: Vec<bool>,
    pub derivation: Vec<DifferenceDerivation>,
    pub contradiction: Option<usize>,
    pub status: ObligationStatus,
    /// Closed nontrivial bounds. Zero is `None`; word identities remain typed
    /// U64 by the input normalizer. Exported only after a complete closure.
    pub bounds: Vec<DifferenceBound>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DifferenceBound {
    pub left: Option<VirValueId>,
    pub right: Option<VirValueId>,
    pub bound: i128,
}

impl DifferenceBound {
    pub(in crate::verifier) fn premise(self) -> DifferencePremise {
        DifferencePremise::Bound {
            left: self.left.map_or(RelationTerm::Constant(0), word),
            right: self.right.map_or(RelationTerm::Constant(0), word),
            bound: self.bound,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DifferenceStop {
    Complete,
    Budget,
    InvalidInput,
    ArithmeticOverflow,
    /// All branches contradict their premises. Not a resource-unreachability
    /// decision: the caller must not turn this into a vacuous safety proof.
    Inconsistent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DifferenceEvidence {
    pub premises: Vec<DifferencePremise>,
    pub goal: DifferenceGoal,
    pub limits: DifferenceLimits,
    pub status: ObligationStatus,
    pub stop: DifferenceStop,
    pub steps: usize,
    pub branches: Vec<DifferenceBranch>,
}

type Edge = (usize, usize, i128, Option<usize>);
type Cell = Option<(i128, usize)>;

struct Query {
    variables: BTreeMap<VirValueId, usize>,
    edges: Vec<Edge>,
    disequalities: Vec<(RelationTerm, RelationTerm, usize)>,
    limits: DifferenceLimits,
    steps: usize,
    derivations: usize,
}

impl Query {
    fn term(&mut self, term: RelationTerm) -> Result<(usize, i128), DifferenceStop> {
        match term {
            RelationTerm::Constant(n) => Ok((0, i128::from(n))),
            RelationTerm::Value {
                value,
                ty: VirType::U64,
            } => {
                if let Some(&id) = self.variables.get(&value) {
                    return Ok((id, 0));
                }
                if self.variables.len() >= self.limits.max_variables {
                    return Err(DifferenceStop::Budget);
                }
                let id = self.variables.len() + 1;
                self.variables.insert(value, id);
                // Every supported variable denotes an unsigned 64-bit word.
                self.push((id, 0, i128::from(u64::MAX), None))?;
                self.push((0, id, 0, None))?;
                Ok((id, 0))
            }
            _ => Err(DifferenceStop::InvalidInput),
        }
    }

    fn push(&mut self, edge: Edge) -> Result<(), DifferenceStop> {
        if self.edges.len() >= self.limits.max_constraints {
            return Err(DifferenceStop::Budget);
        }
        self.edges.push(edge);
        Ok(())
    }

    fn edge(
        &mut self,
        left: RelationTerm,
        right: RelationTerm,
        c: i128,
        origin: usize,
    ) -> Result<Edge, DifferenceStop> {
        let (left, a) = self.term(left)?;
        let (right, b) = self.term(right)?;
        let bound = c
            .checked_sub(a)
            .and_then(|n| n.checked_add(b))
            .ok_or(DifferenceStop::ArithmeticOverflow)?;
        Ok((left, right, bound, Some(origin)))
    }

    fn bound(
        &mut self,
        left: RelationTerm,
        right: RelationTerm,
        c: i128,
        origin: usize,
    ) -> Result<(), DifferenceStop> {
        let edge = self.edge(left, right, c, origin)?;
        self.push(edge)
    }

    fn premise(&mut self, p: &DifferencePremise, origin: usize) -> Result<(), DifferenceStop> {
        match *p {
            DifferencePremise::Interval { value, interval } => {
                let value = word(value);
                self.bound(value, RelationTerm::Constant(interval.upper()), 0, origin)?;
                self.bound(RelationTerm::Constant(interval.lower()), value, 0, origin)
            }
            DifferencePremise::Bound { left, right, bound } => {
                self.bound(left, right, bound, origin)
            }
            DifferencePremise::EqualOffset {
                left,
                right,
                offset,
            } => {
                self.bound(left, right, offset, origin)?;
                self.bound(
                    right,
                    left,
                    offset
                        .checked_neg()
                        .ok_or(DifferenceStop::ArithmeticOverflow)?,
                    origin,
                )
            }
            DifferencePremise::Compare {
                comparison,
                left,
                right,
            } => match comparison {
                RelationComparison::LessThan => self.bound(left, right, -1, origin),
                RelationComparison::LessOrEqual => self.bound(left, right, 0, origin),
                RelationComparison::Equal => {
                    self.bound(left, right, 0, origin)?;
                    self.bound(right, left, 0, origin)
                }
                RelationComparison::NotEqual => {
                    self.term(left)?;
                    self.term(right)?;
                    if self.disequalities.len() >= self.limits.max_constraints {
                        return Err(DifferenceStop::Budget);
                    }
                    self.disequalities.push((left, right, origin));
                    Ok(())
                }
            },
        }
    }

    fn tick(&mut self) -> Result<(), DifferenceStop> {
        if self.steps >= self.limits.max_steps {
            return Err(DifferenceStop::Budget);
        }
        self.steps += 1;
        Ok(())
    }

    fn record(
        &mut self,
        trace: &mut Vec<DifferenceDerivation>,
        node: DifferenceDerivation,
    ) -> Result<usize, DifferenceStop> {
        if self.derivations >= self.limits.max_derivations {
            return Err(DifferenceStop::Budget);
        }
        self.derivations += 1;
        let id = trace.len();
        trace.push(node);
        Ok(id)
    }

    fn branch(
        &mut self,
        choices: Vec<bool>,
        goal: DifferenceGoal,
    ) -> Result<DifferenceBranch, DifferenceStop> {
        let mut edges = self.edges.clone();
        for (i, &choice) in choices.iter().enumerate() {
            let (a, b, origin) = self.disequalities[i];
            edges.push(if choice {
                self.edge(a, b, -1, origin)?
            } else {
                self.edge(b, a, -1, origin)?
            });
        }
        if edges.len() > self.limits.max_constraints {
            return Err(DifferenceStop::Budget);
        }
        let n = self.variables.len() + 1;
        let mut matrix = vec![vec![None; n]; n];
        let mut trace = Vec::new();
        for i in 0..n {
            edges.push((i, i, 0, None));
        }
        for (a, b, c, premise) in edges {
            self.tick()?;
            if matrix[a][b].is_none_or(|(old, _)| c < old) {
                let proof = self.record(
                    &mut trace,
                    DifferenceDerivation::Edge {
                        left: a,
                        right: b,
                        bound: c,
                        premise,
                    },
                )?;
                matrix[a][b] = Some((c, proof));
            }
        }
        for k in 0..n {
            for i in 0..n {
                for j in 0..n {
                    self.tick()?;
                    let (Some((a, first)), Some((b, second))) = (matrix[i][k], matrix[k][j]) else {
                        continue;
                    };
                    let c = a.checked_add(b).ok_or(DifferenceStop::ArithmeticOverflow)?;
                    if matrix[i][j].is_none_or(|(old, _)| c < old) {
                        let proof = self.record(
                            &mut trace,
                            DifferenceDerivation::Compose {
                                first,
                                second,
                                bound: c,
                            },
                        )?;
                        matrix[i][j] = Some((c, proof));
                    }
                }
            }
            if let Some(contradiction) =
                (0..n).find_map(|i| matrix[i][i].filter(|(c, _)| *c < 0).map(|(_, p)| p))
            {
                return Ok(DifferenceBranch {
                    choices,
                    derivation: trace,
                    contradiction: Some(contradiction),
                    status: ObligationStatus::Unknown,
                    bounds: Vec::new(),
                });
            }
        }
        let (l, a) = self.term(goal.left)?;
        let (r, b) = self.term(goal.right)?;
        let bound = b.checked_sub(a).ok_or(DifferenceStop::ArithmeticOverflow)?;
        let reverse = bound
            .checked_neg()
            .ok_or(DifferenceStop::ArithmeticOverflow)?;
        let le = implied(&matrix, l, r, bound);
        let lt = implied(
            &matrix,
            l,
            r,
            bound
                .checked_sub(1)
                .ok_or(DifferenceStop::ArithmeticOverflow)?,
        );
        let ge = implied(&matrix, r, l, reverse);
        let gt = implied(
            &matrix,
            r,
            l,
            reverse
                .checked_sub(1)
                .ok_or(DifferenceStop::ArithmeticOverflow)?,
        );
        let (yes, no) = match goal.comparison {
            RelationComparison::LessThan => (lt, ge),
            RelationComparison::LessOrEqual => (le, gt),
            RelationComparison::Equal => (le && ge, lt || gt),
            RelationComparison::NotEqual => (lt || gt, le && ge),
        };
        let status = if yes {
            ObligationStatus::Proven
        } else if no {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        };
        let mut variables = vec![None; n];
        for (&value, &index) in &self.variables {
            variables[index] = Some(value);
        }
        let mut bounds = Vec::new();
        for i in 0..n {
            for j in 0..n {
                let implicit = if i == 0 { 0 } else { i128::from(u64::MAX) };
                if i != j
                    && let Some((bound, _)) = matrix[i][j]
                    && bound < implicit
                {
                    bounds.push(DifferenceBound {
                        left: variables[i],
                        right: variables[j],
                        bound,
                    });
                }
            }
        }
        bounds.sort();
        Ok(DifferenceBranch {
            choices,
            derivation: trace,
            contradiction: None,
            status,
            bounds,
        })
    }
}

fn implied(matrix: &[Vec<Cell>], left: usize, right: usize, bound: i128) -> bool {
    matrix[left][right].is_some_and(|(c, _)| c <= bound)
}

pub(in crate::verifier) fn word(value: VirValueId) -> RelationTerm {
    RelationTerm::Value {
        value,
        ty: VirType::U64,
    }
}

/// Deterministic, bounded implication under supplied premises. Refuted requires
/// implication of the NEGATION, not merely a model of the negated goal.
/// All budgets are shared by the complete query, including disequality splits.
pub fn solve_difference(
    premises: &[DifferencePremise],
    goal: DifferenceGoal,
    limits: DifferenceLimits,
) -> DifferenceEvidence {
    let mut evidence = DifferenceEvidence {
        premises: Vec::new(),
        goal,
        limits,
        status: ObligationStatus::Unknown,
        stop: DifferenceStop::Complete,
        steps: 0,
        branches: Vec::new(),
    };
    // Bound input copying too, not only closure work.
    if premises.len() > limits.max_constraints {
        evidence.stop = DifferenceStop::Budget;
        return evidence;
    }
    evidence.premises = premises.to_vec();
    let mut query = Query {
        variables: BTreeMap::new(),
        edges: Vec::new(),
        disequalities: Vec::new(),
        limits,
        steps: 0,
        derivations: 0,
    };
    let result = (|| {
        query.term(goal.left)?;
        query.term(goal.right)?;
        for (i, premise) in premises.iter().enumerate() {
            query.premise(premise, i)?;
        }
        let count = 1usize
            .checked_shl(
                u32::try_from(query.disequalities.len()).map_err(|_| DifferenceStop::Budget)?,
            )
            .ok_or(DifferenceStop::Budget)?;
        if count > limits.max_branches {
            return Err(DifferenceStop::Budget);
        }
        for branch in 0..count {
            let choices = (0..query.disequalities.len())
                .map(|i| branch & (1 << i) != 0)
                .collect();
            evidence.branches.push(query.branch(choices, goal)?);
        }
        let mut statuses = evidence
            .branches
            .iter()
            .filter(|b| b.contradiction.is_none())
            .map(|b| b.status);
        let Some(first) = statuses.next() else {
            return Err(DifferenceStop::Inconsistent);
        };
        evidence.status = if statuses.all(|s| s == first) {
            first
        } else {
            ObligationStatus::Unknown
        };
        Ok(())
    })();
    evidence.steps = query.steps;
    if let Err(stop) = result {
        evidence.stop = stop;
        evidence.status = ObligationStatus::Unknown;
    }
    evidence
}

/// Recompute from the original premises, NOT the proposal's premise list.
/// This arithmetic replay does not authenticate the source of those premises;
/// compiler clients must use the enclosing whole-program evidence replay.
pub fn replay_difference(
    premises: &[DifferencePremise],
    goal: DifferenceGoal,
    limits: DifferenceLimits,
    proposal: &DifferenceEvidence,
) -> bool {
    solve_difference(premises, goal, limits) == *proposal
}
