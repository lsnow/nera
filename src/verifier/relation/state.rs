//! Finite numeric component of one guarded resource case. No permissions,
//! memory locations, cached solver success or recursive proof DAG live here.
use std::collections::{BTreeMap, BTreeSet};

use super::difference::{
    DifferenceBound, DifferenceGoal, DifferenceLimits, DifferencePremise, DifferenceStop,
    solve_difference, word,
};
use super::{RelationComparison, RelationTerm};
use crate::{AbstractValue, PathFact, ResourceState, VirIntegerPredicate, VirValueId};

const MAX_FACTS: usize = 64;
type Pair = (Option<VirValueId>, Option<VirValueId>);

/// Immutable numeric endpoint. Literals must survive CFG projection without
/// inventing an SSA carrier; addresses and derived instruction slots are absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RelationOperand {
    Value(VirValueId),
    Constant(u64),
}

impl RelationOperand {
    pub fn value(self) -> Option<VirValueId> {
        match self {
            Self::Value(value) => Some(value),
            Self::Constant(_) => None,
        }
    }

    fn from_term(term: RelationTerm) -> Option<Self> {
        match term {
            RelationTerm::Value {
                value,
                ty: crate::VirType::U64,
            } => Some(Self::Value(value)),
            RelationTerm::Constant(value) => Some(Self::Constant(value)),
            _ => None,
        }
    }

    fn term(self) -> RelationTerm {
        match self {
            Self::Value(value) => word(value),
            Self::Constant(value) => RelationTerm::Constant(value),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RelationPrecisionLoss {
    Budget,
    Projection,
    Widening,
    Inconsistent,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RelationState {
    bounds: BTreeMap<Pair, i128>,
    disequalities: BTreeSet<(RelationOperand, RelationOperand)>,
    losses: BTreeSet<RelationPrecisionLoss>,
}

impl RelationState {
    /// Preserve direct consequences of checked affine values before an edge
    /// drops an operand. For example, `end = start + count` still entails
    /// `start <= end` when only start/end cross the edge. No new closure or
    /// resource observation is performed here.
    pub(in crate::verifier) fn project_affine(
        &self,
        renames: &[(VirValueId, VirValueId)],
        expressions: impl Iterator<Item = (VirValueId, crate::AffineExpression)>,
    ) -> Self {
        let retained: BTreeSet<_> = renames.iter().map(|(source, _)| *source).collect();
        let mut source = self.clone();
        for (value, expression) in expressions {
            if !retained.contains(&value) {
                continue;
            }
            for bound in affine_lower_bounds(value, expression) {
                if bound.left.is_some_and(|root| retained.contains(&root)) {
                    source
                        .bounds
                        .entry((bound.left, bound.right))
                        .and_modify(|old| *old = (*old).min(bound.bound))
                        .or_insert(bound.bound);
                    if source.bounds.len() + source.disequalities.len() > MAX_FACTS {
                        let mut result = self.project(renames);
                        result.losses.insert(RelationPrecisionLoss::Budget);
                        return result;
                    }
                }
            }
        }
        source.project(renames)
    }

    pub const fn new() -> Self {
        Self {
            bounds: BTreeMap::new(),
            disequalities: BTreeSet::new(),
            losses: BTreeSet::new(),
        }
    }
    pub fn bounds(&self) -> impl Iterator<Item = DifferenceBound> + '_ {
        self.bounds
            .iter()
            .map(|(&(left, right), &bound)| DifferenceBound { left, right, bound })
    }
    pub fn disequalities(&self) -> &BTreeSet<(RelationOperand, RelationOperand)> {
        &self.disequalities
    }
    pub fn precision_losses(&self) -> &BTreeSet<RelationPrecisionLoss> {
        &self.losses
    }
    pub(in crate::verifier) fn premises(&self) -> Vec<DifferencePremise> {
        self.bounds()
            .map(DifferenceBound::premise)
            .chain(
                self.disequalities
                    .iter()
                    .map(|&(a, b)| DifferencePremise::Compare {
                        comparison: RelationComparison::NotEqual,
                        left: a.term(),
                        right: b.term(),
                    }),
            )
            .collect()
    }
    fn forget_all(&mut self, reason: RelationPrecisionLoss) {
        self.bounds.clear();
        self.disequalities.clear();
        self.losses.insert(reason);
    }
    pub(in crate::verifier) fn forget_value(&mut self, value: VirValueId) {
        self.bounds
            .retain(|&(a, b), _| a != Some(value) && b != Some(value));
        self.disequalities
            .retain(|&(a, b)| a.value() != Some(value) && b.value() != Some(value));
    }
    pub(in crate::verifier) fn limit(&mut self, limits: DifferenceLimits) {
        let variables: BTreeSet<_> = self
            .bounds
            .keys()
            .flat_map(|(a, b)| a.iter().chain(b))
            .copied()
            .chain(
                self.disequalities
                    .iter()
                    .flat_map(|&(a, b)| [a.value(), b.value()])
                    .flatten(),
            )
            .collect();
        if self.bounds.len() + self.disequalities.len() > limits.max_constraints.min(MAX_FACTS)
            || variables.len() > limits.max_variables
            || limits.max_steps == 0
            || limits.max_derivations == 0
            || limits.max_branches == 0
        {
            self.forget_all(RelationPrecisionLoss::Budget);
        }
    }

    /// Close only facts independently established by a producer and the
    /// current immutable SSA intervals. Failure drops numeric precision only.
    pub(in crate::verifier) fn learn(
        &mut self,
        added: &[DifferencePremise],
        values: &BTreeMap<VirValueId, AbstractValue>,
        limits: DifferenceLimits,
    ) {
        self.limit(limits);
        // Exact immutable words already live in the scalar component. Keeping
        // them as graph vertices creates quadratic, redundant pair bounds and
        // can exhaust the relation budget in otherwise constant code. Resolve
        // these endpoints before closure, but still submit every constraint to
        // the solver: substitution must not hide contradictions or overflow.
        let term = |term| match term {
            RelationTerm::Value {
                value,
                ty: crate::VirType::U64,
            } => match values.get(&value) {
                Some(AbstractValue::U64(interval)) => {
                    interval.exact_value().map_or(term, RelationTerm::Constant)
                }
                _ => term,
            },
            _ => term,
        };
        let mut premises = Vec::new();
        for premise in self.premises().iter().chain(added) {
            let normalized = match *premise {
                DifferencePremise::Bound { left, right, bound } => DifferencePremise::Bound {
                    left: term(left),
                    right: term(right),
                    bound,
                },
                DifferencePremise::EqualOffset {
                    left,
                    right,
                    offset,
                } => DifferencePremise::EqualOffset {
                    left: term(left),
                    right: term(right),
                    offset,
                },
                DifferencePremise::Compare {
                    comparison,
                    left,
                    right,
                } => DifferencePremise::Compare {
                    comparison,
                    left: term(left),
                    right: term(right),
                },
                DifferencePremise::Interval { value, interval } => {
                    let endpoint = term(word(value));
                    if matches!(endpoint, RelationTerm::Constant(_)) {
                        premises.push(DifferencePremise::Bound {
                            left: RelationTerm::Constant(interval.lower()),
                            right: endpoint,
                            bound: 0,
                        });
                        DifferencePremise::Bound {
                            left: endpoint,
                            right: RelationTerm::Constant(interval.upper()),
                            bound: 0,
                        }
                    } else {
                        premise.clone()
                    }
                }
            };
            premises.push(normalized);
        }
        let mut variables = BTreeSet::new();
        for premise in &premises {
            let terms = match *premise {
                DifferencePremise::Bound { left, right, .. }
                | DifferencePremise::EqualOffset { left, right, .. }
                | DifferencePremise::Compare { left, right, .. } => [left, right],
                DifferencePremise::Interval { value, .. } => [word(value), word(value)],
            };
            for term in terms {
                if let RelationTerm::Value { value, .. } = term {
                    variables.insert(value);
                }
            }
        }
        if variables.len() > limits.max_variables
            || premises.len() + variables.len() > limits.max_constraints
        {
            self.forget_all(RelationPrecisionLoss::Budget);
            return;
        }
        for value in variables {
            let Some(AbstractValue::U64(interval)) = values.get(&value) else {
                self.forget_all(RelationPrecisionLoss::Projection);
                return;
            };
            premises.push(DifferencePremise::Interval {
                value,
                interval: *interval,
            });
        }
        let query = solve_difference(
            &premises,
            DifferenceGoal {
                comparison: RelationComparison::Equal,
                left: RelationTerm::Constant(0),
                right: RelationTerm::Constant(0),
            },
            limits,
        );
        if query.stop != DifferenceStop::Complete {
            self.forget_all(if query.stop == DifferenceStop::Inconsistent {
                RelationPrecisionLoss::Inconsistent
            } else {
                RelationPrecisionLoss::Budget
            });
            return;
        }
        let mut branches = query.branches.iter().filter(|b| b.contradiction.is_none());
        let Some(first) = branches.next() else {
            self.forget_all(RelationPrecisionLoss::Inconsistent);
            return;
        };
        let mut bounds: BTreeMap<_, _> = first
            .bounds
            .iter()
            .map(|b| ((b.left, b.right), b.bound))
            .collect();
        for branch in branches {
            let incoming: BTreeMap<_, _> = branch
                .bounds
                .iter()
                .map(|b| ((b.left, b.right), b.bound))
                .collect();
            bounds.retain(|key, bound| {
                if let Some(other) = incoming.get(key) {
                    *bound = (*bound).max(*other);
                    true
                } else {
                    false
                }
            });
        }
        self.disequalities.clear();
        for p in &premises {
            if let DifferencePremise::Compare {
                comparison: RelationComparison::NotEqual,
                left,
                right,
            } = *p
                && let (Some(a), Some(b)) = (
                    RelationOperand::from_term(left),
                    RelationOperand::from_term(right),
                )
                && (a.value().is_some() || b.value().is_some())
            {
                self.disequalities.insert((a.min(b), a.max(b)));
            }
        }
        self.bounds = bounds;
        self.limit(limits);
    }

    /// A target->source map reads the OLD state throughout. One source may
    /// feed several targets; duplicate arguments establish equality. Closed
    /// endpoint bounds survive a dropped intermediate; after widening, facts
    /// requiring a new closure may conservatively be lost here.
    pub(in crate::verifier) fn project(&self, renames: &[(VirValueId, VirValueId)]) -> Self {
        let sources: BTreeMap<_, _> = renames.iter().map(|&(a, b)| (b, a)).collect();
        let mut result = Self {
            losses: self.losses.clone(),
            ..Self::new()
        };
        let mut nodes = vec![(None, None)];
        let tracked: BTreeSet<_> = self
            .bounds
            .keys()
            .flat_map(|(a, b)| a.iter().chain(b))
            .copied()
            .chain(
                self.disequalities
                    .iter()
                    .flat_map(|&(a, b)| [a.value(), b.value()])
                    .flatten(),
            )
            .collect();
        nodes.extend(
            sources
                .iter()
                .map(|(&target, &source)| (Some(target), Some(source))),
        );
        if nodes.len() > 25 {
            result.forget_all(RelationPrecisionLoss::Budget);
            return result;
        }
        for &(target_a, source_a) in &nodes {
            for &(target_b, source_b) in &nodes {
                if target_a == target_b {
                    continue;
                }
                let bound = if source_a == source_b {
                    Some(0)
                } else {
                    self.bounds.get(&(source_a, source_b)).copied()
                };
                if let Some(bound) = bound {
                    result.bounds.insert((target_a, target_b), bound);
                }
            }
        }
        let project_operand = |operand| match operand {
            RelationOperand::Constant(_) => vec![operand],
            RelationOperand::Value(source) => sources
                .iter()
                .filter_map(|(&target, &old)| {
                    (old == source).then_some(RelationOperand::Value(target))
                })
                .collect(),
        };
        for &(a, b) in &self.disequalities {
            for target_a in project_operand(a) {
                for target_b in project_operand(b) {
                    result
                        .disequalities
                        .insert((target_a.min(target_b), target_a.max(target_b)));
                    if result.bounds.len() + result.disequalities.len() > MAX_FACTS {
                        result.forget_all(RelationPrecisionLoss::Budget);
                        return result;
                    }
                }
            }
        }
        if tracked.iter().any(|v| !sources.values().any(|s| s == v)) {
            result.losses.insert(RelationPrecisionLoss::Projection);
        }
        if result.bounds.len() + result.disequalities.len() > MAX_FACTS {
            result.forget_all(RelationPrecisionLoss::Budget);
        }
        result
    }

    pub(in crate::verifier) fn join(&self, other: &Self) -> Self {
        let mut result = Self {
            bounds: self
                .bounds
                .iter()
                .filter_map(|(&key, &bound)| other.bounds.get(&key).map(|b| (key, bound.max(*b))))
                .collect(),
            disequalities: self
                .disequalities
                .intersection(&other.disequalities)
                .copied()
                .collect(),
            losses: self.losses.union(&other.losses).copied().collect(),
        };
        if result.bounds.len() + result.disequalities.len() > MAX_FACTS {
            result.forget_all(RelationPrecisionLoss::Budget);
        }
        result
    }
    /// Standard DBM widening without reclosure: stable bounds survive; an
    /// expanding bound is removed, never incremented indefinitely in a loop.
    pub(in crate::verifier) fn widen(&self, next: &Self) -> Self {
        let mut result = self.join(next);
        result
            .bounds
            .retain(|key, bound| *bound <= self.bounds[key]);
        if result.bounds != self.bounds || result.disequalities != self.disequalities {
            result.losses.insert(RelationPrecisionLoss::Widening);
        }
        result
    }
}

/// A non-wrapping sum of unsigned terms is at least each positive term plus
/// its constant. Both live queries and CFG projection use this same rule.
pub(super) fn affine_lower_bounds(
    value: VirValueId,
    expression: crate::AffineExpression,
) -> impl Iterator<Item = DifferenceBound> {
    expression
        .terms()
        .into_iter()
        .flatten()
        .filter_map(move |(root, scale)| {
            (scale > 0 && root != value).then_some(DifferenceBound {
                left: Some(root),
                right: Some(value),
                bound: -i128::from(expression.addend()),
            })
        })
}

pub(in crate::verifier) fn comparison_premise(
    state: &ResourceState,
    fact: PathFact,
) -> Option<DifferencePremise> {
    let PathFact::Comparison {
        predicate,
        left,
        right,
    } = fact
    else {
        return None;
    };
    let term = |id| match state.value(id) {
        Some(AbstractValue::U64(i)) => {
            Some(i.exact_value().map_or(word(id), RelationTerm::Constant))
        }
        _ => None,
    };
    let (left, right) = (term(left)?, term(right)?);
    let (comparison, left, right) = match predicate {
        VirIntegerPredicate::LessThan => (RelationComparison::LessThan, left, right),
        VirIntegerPredicate::LessOrEqual => (RelationComparison::LessOrEqual, left, right),
        VirIntegerPredicate::Equal => (RelationComparison::Equal, left, right),
        VirIntegerPredicate::NotEqual => (RelationComparison::NotEqual, left, right),
        VirIntegerPredicate::GreaterThan => (RelationComparison::LessThan, right, left),
        VirIntegerPredicate::GreaterOrEqual => (RelationComparison::LessOrEqual, right, left),
    };
    Some(DifferencePremise::Compare {
        comparison,
        left,
        right,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AbstractAllocation, AbstractAllocationId, AbstractLoan, AbstractProvenance, ByteRange,
        LoanActivity, U64Interval, VirBorrowRegionId, VirLoanId, VirLoanKind, VirRegionId,
    };

    fn id(n: u32) -> VirValueId {
        VirValueId::new(n)
    }

    #[test]
    fn affine_edge_projection_keeps_bounds_when_an_operand_dies() {
        let expression = crate::AffineExpression::identity(id(0))
            .checked_add(crate::AffineExpression::identity(id(1)))
            .unwrap()
            .checked_add_constant(3)
            .unwrap();
        let projected = RelationState::new().project_affine(
            &[(id(0), id(10)), (id(2), id(12))],
            [(id(2), expression)].into_iter(),
        );
        assert_eq!(
            projected.bounds().collect::<Vec<_>>(),
            vec![DifferenceBound {
                left: Some(id(10)),
                right: Some(id(12)),
                bound: -3,
            }]
        );
        for a in 0..5 {
            for b in 0..5 {
                assert!(i128::from(a) - i128::from(a + b + 3) <= -3);
            }
        }
        // No expression evidence, wrong endpoint, and a dropped result do not
        // establish a relationship between the remaining coordinates.
        for (renames, expressions) in [
            (vec![(id(0), id(10)), (id(2), id(12))], vec![]),
            (
                vec![(id(3), id(10)), (id(2), id(12))],
                vec![(id(2), expression)],
            ),
            (vec![(id(0), id(10))], vec![(id(2), expression)]),
        ] {
            assert_eq!(
                RelationState::new()
                    .project_affine(&renames, expressions.into_iter())
                    .bounds()
                    .count(),
                0
            );
        }
    }

    #[test]
    fn exact_words_do_not_accumulate_redundant_graph_vertices() {
        let mut state = ResourceState::new();
        state
            .define_value(id(0), AbstractValue::U64(U64Interval::exact(0)))
            .unwrap();
        for n in 1..100 {
            state
                .define_value(id(n), AbstractValue::U64(U64Interval::exact(u64::from(n))))
                .unwrap();
            state.learn_relations(
                &[DifferencePremise::EqualOffset {
                    left: word(id(n)),
                    right: word(id(n - 1)),
                    offset: 1,
                }],
                DifferenceLimits::default(),
            );
            assert!(state.relations().precision_losses().is_empty());
            assert_eq!(state.relations().bounds().count(), 0);
        }
        state
            .define_value(
                id(100),
                AbstractValue::U64(U64Interval::new(0, 100).unwrap()),
            )
            .unwrap();
        state.learn_relations(
            &[DifferencePremise::Bound {
                left: word(id(100)),
                right: word(id(99)),
                bound: -49,
            }],
            DifferenceLimits::default(),
        );
        assert_eq!(
            state.value(id(100)),
            Some(&AbstractValue::U64(U64Interval::new(0, 50).unwrap()))
        );
        assert!(state.relations().precision_losses().is_empty());
        assert!(
            state
                .relations()
                .bounds()
                .any(|bound| bound.left == Some(id(100)))
        );
    }

    #[test]
    fn exact_endpoint_substitution_preserves_failures_and_budget() {
        let values = BTreeMap::from([(id(0), AbstractValue::U64(U64Interval::exact(7)))]);
        for premise in [
            DifferencePremise::Bound {
                left: word(id(0)),
                right: RelationTerm::Constant(6),
                bound: 0,
            },
            DifferencePremise::Interval {
                value: id(0),
                interval: U64Interval::new(0, 6).unwrap(),
            },
            DifferencePremise::Compare {
                comparison: RelationComparison::NotEqual,
                left: word(id(0)),
                right: RelationTerm::Constant(7),
            },
        ] {
            let mut relations = RelationState::new();
            relations.learn(&[premise], &values, DifferenceLimits::default());
            assert!(
                relations
                    .precision_losses()
                    .contains(&RelationPrecisionLoss::Inconsistent)
            );
            assert_eq!(relations.bounds().count(), 0);
        }
        for (offset, limits) in [
            (i128::MIN, DifferenceLimits::default()),
            (
                0,
                DifferenceLimits {
                    max_steps: 0,
                    ..DifferenceLimits::default()
                },
            ),
        ] {
            let mut relations = RelationState::new();
            relations.learn(
                &[DifferencePremise::EqualOffset {
                    left: word(id(0)),
                    right: RelationTerm::Constant(7),
                    offset,
                }],
                &values,
                limits,
            );
            assert!(!relations.precision_losses().is_empty());
            assert_eq!(relations.bounds().count(), 0);
        }
    }

    #[test]
    fn literal_disequality_survives_projection_without_a_constant_slot() {
        let mut state = ResourceState::new();
        state
            .define_value(id(0), AbstractValue::U64(U64Interval::new(0, 8).unwrap()))
            .unwrap();
        state
            .define_value(id(1), AbstractValue::U64(U64Interval::exact(4)))
            .unwrap();
        let premise = comparison_premise(
            &state,
            PathFact::Comparison {
                predicate: VirIntegerPredicate::NotEqual,
                left: id(0),
                right: id(1),
            },
        )
        .unwrap();
        state.learn_relations(&[premise], DifferenceLimits::default());
        assert_eq!(
            state.value(id(0)),
            Some(&AbstractValue::U64(U64Interval::new(0, 8).unwrap()))
        );
        let projected = state
            .project_cfg_case(&[(id(0), id(10)), (id(0), id(11))])
            .unwrap();
        assert!(projected.value(id(1)).is_none());
        for target in [id(10), id(11)] {
            assert!(
                projected
                    .relations()
                    .disequalities()
                    .contains(&(RelationOperand::Value(target), RelationOperand::Constant(4)))
            );
        }
        let query = solve_difference(
            &projected.relations().premises(),
            DifferenceGoal {
                comparison: RelationComparison::NotEqual,
                left: word(id(11)),
                right: RelationTerm::Constant(4),
            },
            DifferenceLimits::default(),
        );
        assert_eq!(query.stop, DifferenceStop::Complete);
        assert_eq!(query.status, crate::ObligationStatus::Proven);
    }

    #[test]
    fn literal_disequality_obeys_mutation_join_widen_and_budget_loss() {
        let mut state = ResourceState::new();
        state
            .define_value(id(0), AbstractValue::U64(U64Interval::new(0, 8).unwrap()))
            .unwrap();
        let original = state.clone();
        state.learn_relations(
            &[DifferencePremise::Compare {
                comparison: RelationComparison::NotEqual,
                left: word(id(0)),
                right: RelationTerm::Constant(4),
            }],
            DifferenceLimits::default(),
        );
        assert!(!state.relations().disequalities().is_empty());
        assert!(
            state
                .join(&original)
                .unwrap()
                .relations()
                .disequalities()
                .is_empty()
        );
        assert!(
            state
                .widen(&original)
                .unwrap()
                .relations()
                .disequalities()
                .is_empty()
        );
        assert!(
            state
                .project_cfg_case(&[])
                .unwrap()
                .relations()
                .disequalities()
                .is_empty()
        );
        let mut changed = state.clone();
        *changed.value_mut(id(0)).unwrap() = AbstractValue::U64(U64Interval::exact(4));
        assert!(changed.relations().disequalities().is_empty());
        state.limit_relations(DifferenceLimits {
            max_variables: 0,
            ..DifferenceLimits::default()
        });
        assert!(state.relations().disequalities().is_empty());
        assert!(
            state
                .relations()
                .precision_losses()
                .contains(&RelationPrecisionLoss::Budget)
        );
    }
    fn bounded_state(offset: i128) -> ResourceState {
        let mut state = ResourceState::new();
        for n in 0..3 {
            state
                .define_value(id(n), AbstractValue::U64(U64Interval::new(0, 5).unwrap()))
                .unwrap();
        }
        state.learn_relations(
            &[
                DifferencePremise::EqualOffset {
                    left: word(id(1)),
                    right: word(id(0)),
                    offset,
                },
                DifferencePremise::Bound {
                    left: word(id(1)),
                    right: word(id(2)),
                    bound: 0,
                },
            ],
            DifferenceLimits::default(),
        );
        state
    }
    fn contains(state: &ResourceState, concrete: &[u64; 3]) -> bool {
        (0..3).all(|n| matches!(state.value(id(n)),Some(AbstractValue::U64(interval)) if interval.contains(concrete[n as usize])))
            && state.relations().bounds().all(|b| {
                let value = |v: Option<VirValueId>| v.map_or(0,|id| i128::from(concrete[id.get() as usize]));
                value(b.left) - value(b.right) <= b.bound
            })
            && state.relations().disequalities().iter().all(|&(a,b)| {
                let value = |term| match term {
                    RelationOperand::Value(id) => concrete[id.get() as usize],
                    RelationOperand::Constant(value) => value,
                };
                value(a) != value(b)
            })
    }

    #[test]
    fn resource_join_and_widen_concretization_includes_both_numeric_and_resource_cases() {
        for a in 0..=2 {
            for b in 0..=2 {
                let mut left = bounded_state(a);
                let mut right = bounded_state(b);
                let allocation = AbstractAllocationId::new(0);
                for state in [&mut left, &mut right] {
                    state
                        .define_allocation(
                            allocation,
                            AbstractAllocation::new(VirRegionId::new(0), 8, 8).unwrap(),
                        )
                        .unwrap();
                    state
                        .define_loan(
                            VirLoanId::new(0),
                            AbstractLoan::new(
                                AbstractProvenance::Known(allocation),
                                ByteRange::new(0, 8).unwrap(),
                                VirLoanKind::Shared,
                                VirBorrowRegionId::new(0),
                                None,
                                LoanActivity::Active,
                            ),
                        )
                        .unwrap();
                }
                left.allocation_mut(allocation)
                    .unwrap()
                    .mark_initialized(ByteRange::new(0, 8).unwrap())
                    .unwrap();
                let joined = left.join(&right).unwrap();
                let widened = left.widen(&joined).unwrap();
                assert_eq!(joined, left.join(&right).unwrap());
                assert_eq!(joined, right.join(&left).unwrap());
                assert_eq!(joined, joined.join(&joined).unwrap());
                for model in (0..216).map(|n| [n % 6, (n / 6) % 6, n / 36]) {
                    let satisfies = |offset| {
                        i128::from(model[1]) - i128::from(model[0]) == offset
                            && model[1] <= model[2]
                    };
                    if satisfies(a) {
                        assert!(contains(&left, &model));
                    }
                    if satisfies(b) {
                        assert!(contains(&right, &model));
                    }
                    if satisfies(a) || satisfies(b) {
                        assert!(contains(&joined, &model));
                        assert!(contains(&widened, &model));
                    }
                }
                for state in [&joined, &widened] {
                    assert_eq!(
                        state.loan(VirLoanId::new(0)).unwrap().activity(),
                        LoanActivity::Active
                    );
                    assert!(
                        state
                            .allocation(allocation)
                            .unwrap()
                            .initialization()
                            .initialized()
                            .is_empty()
                    );
                }
                let mut lost = left.clone();
                lost.limit_relations(DifferenceLimits {
                    max_variables: 0,
                    ..DifferenceLimits::default()
                });
                assert_eq!(left.loans(), lost.loans());
                assert_eq!(left.allocations(), lost.allocations());
                assert_eq!(left.values(), lost.values());
            }
        }
    }

    #[test]
    fn simultaneous_phi_swap_duplicate_arguments_and_eliminated_intermediate() {
        let original = bounded_state(1);
        let swapped = original
            .project_cfg_case(&[(id(0), id(1)), (id(1), id(0)), (id(2), id(2))])
            .unwrap();
        assert!(
            swapped
                .relations()
                .bounds()
                .any(|b| b.left == Some(id(1)) && b.right == Some(id(0)) && b.bound == -1)
        );
        let projected = original
            .project_cfg_case(&[(id(0), id(10)), (id(2), id(20))])
            .unwrap();
        assert!(
            projected
                .relations()
                .bounds()
                .any(|b| b.left == Some(id(10)) && b.right == Some(id(20)) && b.bound <= -1)
        );
        assert!(projected.relations().bounds().all(|b| {
            [b.left, b.right]
                .into_iter()
                .flatten()
                .all(|v| [id(10), id(20)].contains(&v))
        }));
        let duplicated = original
            .project_cfg_case(&[(id(0), id(10)), (id(0), id(11))])
            .unwrap();
        for (a, b) in [(10, 11), (11, 10)] {
            assert!(
                duplicated
                    .relations()
                    .bounds()
                    .any(|edge| edge.left == Some(id(a))
                        && edge.right == Some(id(b))
                        && edge.bound == 0)
            );
        }
    }

    #[test]
    fn widening_is_finite_and_mutable_value_access_forgets_incident_relations() {
        let mut state = bounded_state(0).relations().clone();
        for offset in 1..40 {
            let next = state.join(bounded_state(offset.min(4)).relations());
            let previous_keys: BTreeSet<_> = state.bounds.keys().copied().collect();
            state = state.widen(&next);
            assert!(state.bounds.keys().all(|key| previous_keys.contains(key)));
        }
        let stable = state.widen(&state);
        assert_eq!(state, stable);
        let mut state = bounded_state(1);
        *state.value_mut(id(0)).unwrap() = AbstractValue::U64(U64Interval::unknown());
        assert!(
            state
                .relations()
                .bounds()
                .all(|b| b.left != Some(id(0)) && b.right != Some(id(0)))
        );
    }
}
