use std::collections::BTreeSet;

#[cfg(test)]
mod initialization_tests;

use super::resource::{
    LoanPrecisionLoss, PathCondition, ResourceCase, ResourceJoinError, ResourceState,
};

/// Why a guarded state had to conservatively discard conditional precision.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GuardedStatePrecisionLoss {
    CaseBudget,
    GuardAtomBudget,
    GuardProjection,
    LoopWidening,
    RefinementPassBudget,
    RefinementVisitBudget,
    ActiveLoanBudget,
    LoanAliasBudget,
    RegionConstraintBudget,
    ReborrowDepthBudget,
    LoanJoin,
    LoanLoopWidening,
}

/// Deterministic limits applied while normalizing one guarded state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct GuardedStateLimits {
    pub max_cases: usize,
    pub max_guard_atoms: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum GuardedReduction {
    /// Merge cases whose memory/resource projection is identical. This is the
    /// ordinary inexpensive path used by the fixed-point analysis.
    Selective,
    /// Retain scalar-only partitions while replaying an Unknown obligation.
    PreserveGuards,
}

/// A finite disjunction of whole [`ResourceCase`] values.
///
/// The guard is the case's existing [`super::resource::PathCondition`]; allocation, pointer,
/// permission and object-payload facts remain in the same `ResourceState`.
/// This wrapper therefore adds no parallel ownership or transfer domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConditionalResourceState {
    cases: Vec<ResourceCase>,
    precision_losses: BTreeSet<GuardedStatePrecisionLoss>,
}

impl ConditionalResourceState {
    #[must_use]
    pub fn singleton(state: ResourceCase) -> Self {
        let cases = if state.path_condition().is_reachable() {
            vec![state]
        } else {
            Vec::new()
        };
        Self {
            cases,
            precision_losses: BTreeSet::new(),
        }
    }

    #[must_use]
    pub const fn unreachable() -> Self {
        Self {
            cases: Vec::new(),
            precision_losses: BTreeSet::new(),
        }
    }

    #[must_use]
    pub fn cases(&self) -> &[ResourceCase] {
        &self.cases
    }

    #[must_use]
    pub const fn precision_losses(&self) -> &BTreeSet<GuardedStatePrecisionLoss> {
        &self.precision_losses
    }

    #[must_use]
    pub fn is_reachable(&self) -> bool {
        !self.cases.is_empty()
    }

    #[must_use]
    pub fn is_precise(&self) -> bool {
        self.precision_losses.is_empty()
    }

    /// Pointwise view retained for the existing public CFG API.
    pub fn collapsed(&self) -> Result<ResourceState, ResourceJoinError> {
        collapse_cases(&self.cases)
    }

    pub(super) fn from_cases(
        cases: Vec<ResourceCase>,
        inherited_losses: BTreeSet<GuardedStatePrecisionLoss>,
        limits: GuardedStateLimits,
        reduction: GuardedReduction,
    ) -> Result<Self, ResourceJoinError> {
        normalize(cases, inherited_losses, limits, reduction)
    }

    pub(super) fn join(
        &self,
        other: &Self,
        limits: GuardedStateLimits,
        reduction: GuardedReduction,
    ) -> Result<Self, ResourceJoinError> {
        let mut cases = self.cases.clone();
        cases.extend(other.cases.iter().cloned());
        let mut losses = self.precision_losses.clone();
        losses.extend(other.precision_losses.iter().copied());
        normalize(cases, losses, limits, reduction)
    }

    pub(super) fn widen(
        &self,
        next: &Self,
        limits: GuardedStateLimits,
    ) -> Result<Self, ResourceJoinError> {
        let mut losses = self.precision_losses.clone();
        losses.extend(next.precision_losses.iter().copied());

        let guards_match = self.cases.len() == next.cases.len()
            && self
                .cases
                .iter()
                .zip(&next.cases)
                .all(|(current, next)| current.path_condition() == next.path_condition());
        if guards_match {
            let cases = self
                .cases
                .iter()
                .zip(&next.cases)
                .map(|(current, next)| current.widen(next))
                .collect::<Result<Vec<_>, _>>()?;
            normalize(cases, losses, limits, GuardedReduction::Selective)
        } else {
            losses.insert(GuardedStatePrecisionLoss::LoopWidening);
            let current = self.collapsed()?;
            let next = next.collapsed()?;
            normalize(
                vec![current.widen(&next)?],
                losses,
                limits,
                GuardedReduction::Selective,
            )
        }
    }

    pub(super) fn collapse_for_loop(
        &self,
        limits: GuardedStateLimits,
    ) -> Result<Self, ResourceJoinError> {
        let mut losses = self.precision_losses.clone();
        losses.insert(GuardedStatePrecisionLoss::LoopWidening);
        normalize(
            vec![self.collapsed()?],
            losses,
            limits,
            GuardedReduction::Selective,
        )
    }
}

fn normalize(
    mut cases: Vec<ResourceCase>,
    mut losses: BTreeSet<GuardedStatePrecisionLoss>,
    limits: GuardedStateLimits,
    reduction: GuardedReduction,
) -> Result<ConditionalResourceState, ResourceJoinError> {
    cases.retain(|case| case.path_condition().is_reachable());
    for case in &cases {
        losses.extend(
            case.loan_precision_losses()
                .iter()
                .copied()
                .map(guarded_loan_loss),
        );
    }
    for case in &mut cases {
        if case.path_condition().atom_count() > limits.max_guard_atoms {
            case.forget_path_condition();
            losses.insert(GuardedStatePrecisionLoss::GuardAtomBudget);
        }
    }
    cases.sort_by(|left, right| left.path_condition().cmp(right.path_condition()));
    match reduction {
        GuardedReduction::Selective => {
            cases = merge_equal_guards(cases)?;
            cases = merge_resource_equivalent(cases)?;
            cases.sort_by(|left, right| left.path_condition().cmp(right.path_condition()));
            cases = merge_equal_guards(cases)?;
        }
        GuardedReduction::PreserveGuards => {
            // Obligation-directed replay is a bounded disjunctive analysis.
            // Two predecessor states can remain semantically distinct even
            // when their branch atom was not projected onto the join block:
            // a carried Bool drop flag can still select the right effect in
            // each complete ResourceCase. Only exact duplicates are removed.
            cases = deduplicate_identical_cases(cases);
        }
    }

    if limits.max_cases == 0 && !cases.is_empty() {
        losses.insert(GuardedStatePrecisionLoss::CaseBudget);
    }
    if cases.len() > limits.max_cases.max(1) {
        cases = vec![collapse_cases(&cases)?];
        losses.insert(GuardedStatePrecisionLoss::CaseBudget);
    }

    Ok(ConditionalResourceState {
        cases,
        precision_losses: losses,
    })
}

const fn guarded_loan_loss(loss: LoanPrecisionLoss) -> GuardedStatePrecisionLoss {
    match loss {
        LoanPrecisionLoss::ActiveLoanBudget => GuardedStatePrecisionLoss::ActiveLoanBudget,
        LoanPrecisionLoss::LoanAliasBudget => GuardedStatePrecisionLoss::LoanAliasBudget,
        LoanPrecisionLoss::RegionConstraintBudget => {
            GuardedStatePrecisionLoss::RegionConstraintBudget
        }
        LoanPrecisionLoss::ReborrowDepthBudget => GuardedStatePrecisionLoss::ReborrowDepthBudget,
        LoanPrecisionLoss::LoanJoin => GuardedStatePrecisionLoss::LoanJoin,
        LoanPrecisionLoss::LoanLoopWidening => GuardedStatePrecisionLoss::LoanLoopWidening,
    }
}

fn deduplicate_identical_cases(cases: Vec<ResourceCase>) -> Vec<ResourceCase> {
    let mut unique = Vec::with_capacity(cases.len());
    for case in cases {
        if !unique.contains(&case) {
            unique.push(case);
        }
    }
    unique
}

fn merge_equal_guards(cases: Vec<ResourceCase>) -> Result<Vec<ResourceCase>, ResourceJoinError> {
    let mut merged: Vec<ResourceCase> = Vec::with_capacity(cases.len());
    for case in cases {
        if let Some(previous) = merged.iter_mut().find(|previous| {
            previous.path_condition() == case.path_condition()
                && previous.same_resource_facts(&case)
        }) {
            *previous = previous.join(&case)?;
        } else {
            merged.push(case);
        }
    }
    Ok(merged)
}

fn merge_resource_equivalent(
    mut cases: Vec<ResourceCase>,
) -> Result<Vec<ResourceCase>, ResourceJoinError> {
    // Joining two conjunctions by intersecting their atoms is exact only
    // when they differ by one complementary fact.  Merging arbitrary
    // resource-equivalent guards would turn `(not a) or (a and not b)` into
    // `true`; that overlaps a third `(a and b)` case with different ownership
    // and loses precisely the correlation guarded state is meant to retain.
    loop {
        let mut merged = false;
        'search: for index in 0..cases.len() {
            for candidate in index + 1..cases.len() {
                if cases[index].same_resource_facts(&cases[candidate])
                    && guards_have_exact_conjunctive_union(
                        cases[index].path_condition(),
                        cases[candidate].path_condition(),
                    )
                {
                    let right = cases.remove(candidate);
                    cases[index] = cases[index].join(&right)?;
                    merged = true;
                    break 'search;
                }
            }
        }
        if !merged {
            break;
        }
    }
    Ok(cases)
}

fn guards_have_exact_conjunctive_union(left: &PathCondition, right: &PathCondition) -> bool {
    let (Some(left), Some(right)) = (left.facts(), right.facts()) else {
        return false;
    };
    let left_only = left.difference(right).copied().collect::<Vec<_>>();
    let right_only = right.difference(left).copied().collect::<Vec<_>>();
    matches!((left_only.as_slice(), right_only.as_slice()), ([left], [right]) if left.negated() == *right)
}

fn collapse_cases(cases: &[ResourceCase]) -> Result<ResourceState, ResourceJoinError> {
    let mut collapsed = ResourceState::unreachable();
    for case in cases {
        collapsed = collapsed.join(case)?;
    }
    Ok(collapsed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        VirValueId,
        verifier::{
            AbstractAllocationId, AbstractPointer, AbstractProvenance, AbstractValue,
            GuaranteedAlignment, PathCondition, PathFact, U64Interval,
        },
    };

    fn guarded(value: u32, expected: bool) -> ResourceState {
        let mut state = ResourceState::new();
        state.conjoin_path_fact(PathFact::boolean(VirValueId::new(value), expected));
        state
    }

    fn guarded_pointer(guard: u32, allocation: u32) -> ResourceState {
        guarded_pointer_value(guard, true, allocation)
    }

    fn guarded_pointer_value(guard: u32, expected: bool, allocation: u32) -> ResourceState {
        let mut state = guarded(guard, expected);
        state
            .define_value(
                VirValueId::new(100),
                AbstractValue::Pointer(AbstractPointer::new(
                    AbstractProvenance::Known(AbstractAllocationId::new(allocation)),
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )),
            )
            .unwrap();
        state
    }

    #[test]
    fn selective_reduction_collapses_scalar_only_partitions() {
        let limits = GuardedStateLimits {
            max_cases: 8,
            max_guard_atoms: 8,
        };
        let state = ConditionalResourceState::from_cases(
            vec![guarded(0, false), guarded(0, true)],
            BTreeSet::new(),
            limits,
            GuardedReduction::Selective,
        )
        .unwrap();
        assert_eq!(state.cases().len(), 1);
        assert_eq!(state.cases()[0].path_condition(), &PathCondition::empty());
    }

    #[test]
    fn precise_replay_retains_distinct_cases_after_guard_projection() {
        let limits = GuardedStateLimits {
            max_cases: 8,
            max_guard_atoms: 8,
        };
        let mut first = ResourceState::new();
        first
            .define_value(
                VirValueId::new(100),
                AbstractValue::Pointer(AbstractPointer::new(
                    AbstractProvenance::Known(AbstractAllocationId::new(1)),
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )),
            )
            .unwrap();
        let mut second = ResourceState::new();
        second
            .define_value(
                VirValueId::new(100),
                AbstractValue::Pointer(AbstractPointer::new(
                    AbstractProvenance::Known(AbstractAllocationId::new(2)),
                    U64Interval::exact(0),
                    GuaranteedAlignment::new(8).unwrap(),
                )),
            )
            .unwrap();

        let state = ConditionalResourceState::from_cases(
            vec![first.clone(), first, second],
            BTreeSet::new(),
            limits,
            GuardedReduction::PreserveGuards,
        )
        .unwrap();

        assert_eq!(state.cases().len(), 2);
        assert!(
            state
                .cases()
                .iter()
                .all(|case| case.path_condition() == &PathCondition::empty())
        );
    }

    #[test]
    fn selective_reduction_preserves_resource_cases_with_the_same_guard() {
        let state = ConditionalResourceState::from_cases(
            vec![guarded_pointer(0, 1), guarded_pointer(0, 2)],
            BTreeSet::new(),
            GuardedStateLimits {
                max_cases: 8,
                max_guard_atoms: 8,
            },
            GuardedReduction::Selective,
        )
        .unwrap();

        assert_eq!(state.cases().len(), 2);
        let provenances = state
            .cases()
            .iter()
            .map(|case| match case.value(VirValueId::new(100)) {
                Some(AbstractValue::Pointer(pointer)) => pointer.provenance(),
                _ => panic!("resource pointer remains typed"),
            })
            .collect::<Vec<_>>();
        assert!(provenances.contains(&AbstractProvenance::Known(AbstractAllocationId::new(1))));
        assert!(provenances.contains(&AbstractProvenance::Known(AbstractAllocationId::new(2))));
    }

    #[test]
    fn non_conjunctive_nested_guard_union_is_not_over_reduced() {
        let outer_false = guarded_pointer_value(0, false, 1);
        let mut outer_true_inner_false = guarded_pointer(0, 1);
        outer_true_inner_false.conjoin_path_fact(PathFact::boolean(VirValueId::new(1), false));
        let mut outer_true_inner_true = guarded_pointer(0, 2);
        outer_true_inner_true.conjoin_path_fact(PathFact::boolean(VirValueId::new(1), true));

        let state = ConditionalResourceState::from_cases(
            vec![outer_false, outer_true_inner_false, outer_true_inner_true],
            BTreeSet::new(),
            GuardedStateLimits {
                max_cases: 8,
                max_guard_atoms: 8,
            },
            GuardedReduction::Selective,
        )
        .unwrap();

        assert_eq!(state.cases().len(), 3);
        assert!(state.cases().iter().all(|case| {
            case.path_condition()
                .facts()
                .is_some_and(|facts| !facts.is_empty())
        }));
    }

    #[test]
    fn budget_collapse_concretization_covers_every_input_case() {
        fn guard_accepts(condition: &PathCondition, assignment: bool) -> bool {
            condition.facts().is_some_and(|facts| {
                facts.iter().all(|fact| match *fact {
                    PathFact::Boolean { value, expected } if value == VirValueId::new(0) => {
                        assignment == expected
                    }
                    _ => true,
                })
            })
        }

        fn provenance_covers(output: AbstractProvenance, input: AbstractProvenance) -> bool {
            output == AbstractProvenance::Unknown || output == input
        }

        let inputs = [
            guarded_pointer_value(0, false, 1),
            guarded_pointer_value(0, true, 2),
        ];
        let collapsed = ConditionalResourceState::from_cases(
            inputs.to_vec(),
            BTreeSet::new(),
            GuardedStateLimits {
                max_cases: 1,
                max_guard_atoms: 8,
            },
            GuardedReduction::PreserveGuards,
        )
        .unwrap();

        for assignment in [false, true] {
            for input in inputs
                .iter()
                .filter(|input| guard_accepts(input.path_condition(), assignment))
            {
                let Some(AbstractValue::Pointer(input_pointer)) = input.value(VirValueId::new(100))
                else {
                    panic!("input pointer remains typed");
                };
                assert!(collapsed.cases().iter().any(|output| {
                    let Some(AbstractValue::Pointer(output_pointer)) =
                        output.value(VirValueId::new(100))
                    else {
                        return false;
                    };
                    guard_accepts(output.path_condition(), assignment)
                        && provenance_covers(
                            output_pointer.provenance(),
                            input_pointer.provenance(),
                        )
                }));
            }
        }
    }

    #[test]
    fn guarded_loan_concretization_covers_activity_provenance_and_aliases() {
        use crate::{
            AbstractLoan, ByteRange, LoanActivity, VirBorrowRegionId, VirLoanId, VirLoanKind,
        };

        let id = VirLoanId::new(0);
        let guard = VirValueId::new(0);
        let activities = [
            LoanActivity::Active,
            LoanActivity::Suspended,
            LoanActivity::Ended,
        ];
        for left in activities {
            for right in activities {
                let inputs = [left, right]
                    .into_iter()
                    .enumerate()
                    .map(|(index, activity)| {
                        let mut state = ResourceState::new();
                        state.conjoin_path_fact(PathFact::boolean(guard, index != 0));
                        let mut loan = AbstractLoan::new(
                            AbstractProvenance::Known(AbstractAllocationId::new(index as u32)),
                            ByteRange::new(0, 8).unwrap(),
                            VirLoanKind::Shared,
                            VirBorrowRegionId::new(0),
                            None,
                            activity,
                        );
                        if activity != LoanActivity::Ended {
                            loan.add_authority(VirValueId::new(index as u32 + 10));
                        }
                        state.define_loan(id, loan).unwrap();
                        state
                    })
                    .collect::<Vec<_>>();
                for max_cases in [1, 2] {
                    for max_guard_atoms in [0, 1] {
                        let limits = GuardedStateLimits {
                            max_cases,
                            max_guard_atoms,
                        };
                        let output = ConditionalResourceState::from_cases(
                            inputs.clone(),
                            BTreeSet::new(),
                            limits,
                            GuardedReduction::Selective,
                        )
                        .unwrap();
                        assert_eq!(
                            output,
                            ConditionalResourceState::from_cases(
                                inputs.clone(),
                                BTreeSet::new(),
                                limits,
                                GuardedReduction::Selective
                            )
                            .unwrap()
                        );
                        // Independent finite concretization: every concrete
                        // Boolean branch and lifecycle state must be covered.
                        // Alias sets are MAY sets, never a grant of permission.
                        for (index, input) in inputs.iter().enumerate() {
                            let input_loan = input.loan(id).unwrap();
                            assert!(
                                output.cases().iter().any(|case| {
                                    let guard_covers =
                                        case.path_condition().facts().is_some_and(|facts| {
                                            facts.iter().all(|fact| match *fact {
                                                PathFact::Boolean { value, expected }
                                                    if value == guard =>
                                                {
                                                    expected == (index != 0)
                                                }
                                                _ => false,
                                            })
                                        });
                                    let loan = case.loan(id).unwrap();
                                    guard_covers
                                        && (loan.activity() == LoanActivity::MaybeActive
                                            || loan.activity() == input_loan.activity())
                                        && (loan.provenance() == AbstractProvenance::Unknown
                                            || loan.provenance() == input_loan.provenance())
                                        && loan.authorities().is_superset(input_loan.authorities())
                                        && loan.range() == input_loan.range()
                                        && loan.kind() == input_loan.kind()
                                        && loan.parent() == input_loan.parent()
                                        && loan.region() == input_loan.region()
                                }),
                                "lost branch {index} for {left:?}/{right:?} under {limits:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn case_and_guard_budgets_only_lose_precision() {
        let state = ConditionalResourceState::from_cases(
            vec![guarded(0, false), guarded(0, true)],
            BTreeSet::new(),
            GuardedStateLimits {
                max_cases: 1,
                max_guard_atoms: 0,
            },
            GuardedReduction::PreserveGuards,
        )
        .unwrap();
        assert_eq!(state.cases().len(), 1);
        assert_eq!(state.cases()[0].path_condition(), &PathCondition::empty());
        assert!(
            state
                .precision_losses()
                .contains(&GuardedStatePrecisionLoss::GuardAtomBudget)
        );
    }

    #[test]
    fn guarded_union_is_a_semilattice_before_budget_reduction() {
        let limits = GuardedStateLimits {
            max_cases: 8,
            max_guard_atoms: 8,
        };
        let states = [
            ConditionalResourceState::singleton(guarded_pointer(0, 1)),
            ConditionalResourceState::singleton(guarded_pointer(1, 2)),
            ConditionalResourceState::singleton(guarded_pointer(2, 3)),
        ];
        for left in &states {
            assert_eq!(
                left.join(left, limits, GuardedReduction::Selective)
                    .unwrap(),
                *left
            );
            for right in &states {
                assert_eq!(
                    left.join(right, limits, GuardedReduction::Selective)
                        .unwrap(),
                    right
                        .join(left, limits, GuardedReduction::Selective)
                        .unwrap()
                );
                for third in &states {
                    assert_eq!(
                        left.join(right, limits, GuardedReduction::Selective)
                            .unwrap()
                            .join(third, limits, GuardedReduction::Selective)
                            .unwrap(),
                        left.join(
                            &right
                                .join(third, limits, GuardedReduction::Selective)
                                .unwrap(),
                            limits,
                            GuardedReduction::Selective,
                        )
                        .unwrap()
                    );
                }
            }
        }
    }

    #[test]
    fn mismatched_loop_guards_collapse_and_report_precision_loss() {
        let limits = GuardedStateLimits {
            max_cases: 4,
            max_guard_atoms: 4,
        };
        let current = ConditionalResourceState::singleton(guarded_pointer(0, 1));
        let next = ConditionalResourceState::singleton(guarded_pointer(1, 2));

        let widened = current.widen(&next, limits).expect("widen succeeds");

        assert_eq!(widened.cases().len(), 1);
        assert!(
            widened
                .precision_losses()
                .contains(&GuardedStatePrecisionLoss::LoopWidening)
        );
    }

    #[test]
    fn case_budget_joins_conflicting_pointer_identity_instead_of_choosing_one() {
        let state = ConditionalResourceState::from_cases(
            vec![guarded_pointer(0, 1), guarded_pointer(1, 2)],
            BTreeSet::new(),
            GuardedStateLimits {
                max_cases: 1,
                max_guard_atoms: 8,
            },
            GuardedReduction::PreserveGuards,
        )
        .unwrap();
        let Some(AbstractValue::Pointer(pointer)) = state.cases()[0].value(VirValueId::new(100))
        else {
            panic!("joined pointer remains typed");
        };
        assert_eq!(pointer.provenance(), AbstractProvenance::Unknown);
    }
}
