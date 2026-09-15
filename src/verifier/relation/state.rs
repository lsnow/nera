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
    disequalities: BTreeSet<(VirValueId, VirValueId)>,
    losses: BTreeSet<RelationPrecisionLoss>,
}

impl RelationState {
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
    pub fn disequalities(&self) -> &BTreeSet<(VirValueId, VirValueId)> {
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
                        left: word(a),
                        right: word(b),
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
            .retain(|&(a, b)| a != value && b != value);
    }
    pub(in crate::verifier) fn limit(&mut self, limits: DifferenceLimits) {
        let variables: BTreeSet<_> = self
            .bounds
            .keys()
            .flat_map(|(a, b)| a.iter().chain(b))
            .copied()
            .chain(self.disequalities.iter().flat_map(|&(a, b)| [a, b]))
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
        let mut premises = self.premises();
        premises.extend_from_slice(added);
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
        for p in added {
            if let DifferencePremise::Compare {
                comparison: RelationComparison::NotEqual,
                left: RelationTerm::Value { value: a, .. },
                right: RelationTerm::Value { value: b, .. },
            } = *p
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
            .chain(self.disequalities.iter().flat_map(|&(a, b)| [a, b]))
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
                if let (Some(a), Some(b), Some(ta), Some(tb)) =
                    (source_a, source_b, target_a, target_b)
                    && self.disequalities.contains(&(a.min(b), a.max(b)))
                {
                    result.disequalities.insert((ta.min(tb), ta.max(tb)));
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
            && state.relations().disequalities().iter().all(|&(a,b)|concrete[a.get() as usize] != concrete[b.get() as usize])
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
