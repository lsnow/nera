//! Query projection from current intervals, guards, affine and CFG relations.
use std::collections::BTreeSet;

use super::difference::{
    DifferenceEvidence, DifferenceGoal, DifferenceLimits, DifferencePremise, DifferenceStop,
    solve_difference, word,
};
use super::{RelationComparison, RelationTerm, kernel};
use crate::{
    AbstractValue, ObligationStatus, PathFact, ResourceState, U64Interval, VirIntegerPredicate,
    VirType, VirValueId,
};

pub(super) fn interval(state: &ResourceState, term: RelationTerm) -> Option<U64Interval> {
    match term {
        RelationTerm::Constant(n) => Some(U64Interval::exact(n)),
        RelationTerm::Value {
            value,
            ty: VirType::U64,
        } => match state.value(value)? {
            AbstractValue::U64(interval) => Some(*interval),
            _ => None,
        },
        _ => None,
    }
}

fn insert(
    values: &mut BTreeSet<VirValueId>,
    value: VirValueId,
    limits: DifferenceLimits,
) -> Result<(), DifferenceStop> {
    if !values.contains(&value) && values.len() >= limits.max_variables {
        return Err(DifferenceStop::Budget);
    }
    values.insert(value);
    Ok(())
}

/// Retain only the connected, supported part of the current query. Intervals
/// and unit-scale affine equalities come from existing production transfers;
/// guards are actual path facts, never pending memory obligations or booleans
/// that merely happened to be compared. Different loads remain distinct SSA.
pub(super) fn project(
    state: &ResourceState,
    goal: DifferenceGoal,
    limits: DifferenceLimits,
) -> Result<Vec<DifferencePremise>, DifferenceStop> {
    let mut values = BTreeSet::new();
    for term in [goal.left, goal.right] {
        if let RelationTerm::Value { value, .. } = term {
            insert(&mut values, value, limits)?;
        }
    }
    let facts = state
        .path_condition()
        .facts()
        .ok_or(DifferenceStop::Inconsistent)?;
    let relations = state.relations().premises();
    // Existing guards have their own CFG budget; still charge this query for
    // scanning/projecting them, so closure is not the only bounded operation.
    let mut visits = 0usize;
    loop {
        let old = values.len();
        for value in values.clone() {
            visits = visits.checked_add(1).ok_or(DifferenceStop::Budget)?;
            if visits > limits.max_steps {
                return Err(DifferenceStop::Budget);
            }
            if let Some(expression) = state.word_expression(value) {
                if expression.scale() == 1 {
                    if let Some(root) = expression.root() {
                        if interval(state, word(root)).is_some() {
                            insert(&mut values, root, limits)?;
                        }
                    }
                }
            }
        }
        for fact in facts {
            visits = visits.checked_add(1).ok_or(DifferenceStop::Budget)?;
            if visits > limits.max_steps {
                return Err(DifferenceStop::Budget);
            }
            if let PathFact::Comparison { left, right, .. } = *fact {
                if (values.contains(&left) || values.contains(&right))
                    && interval(state, word(left)).is_some()
                    && interval(state, word(right)).is_some()
                {
                    insert(&mut values, left, limits)?;
                    insert(&mut values, right, limits)?;
                }
            }
        }
        for premise in &relations {
            visits = visits.checked_add(1).ok_or(DifferenceStop::Budget)?;
            if visits > limits.max_steps {
                return Err(DifferenceStop::Budget);
            }
            let (DifferencePremise::Bound { left, right, .. }
            | DifferencePremise::Compare { left, right, .. }) = *premise
            else {
                continue;
            };
            let endpoints = [left, right]
                .into_iter()
                .filter_map(|term| {
                    if let RelationTerm::Value { value, .. } = term {
                        Some(value)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            if endpoints.iter().any(|id| values.contains(id)) {
                for id in endpoints {
                    if interval(state, word(id)).is_some() {
                        insert(&mut values, id, limits)?;
                    }
                }
            }
        }
        if values.len() == old {
            break;
        }
    }
    let mut premises = Vec::new();
    let mut push = |mut premise| {
        // CFG closure can retain the same disequality through several SSA
        // identity aliases. It is one split, not 2^aliases independent cases.
        if let DifferencePremise::Compare {
            comparison: RelationComparison::NotEqual,
            left,
            right,
        } = premise
        {
            let root = |term| match term {
                RelationTerm::Value { value, .. } => state
                    .word_expression(value)
                    .filter(|e| e.scale() == 1 && e.addend() == 0)
                    .and_then(|e| e.root())
                    .filter(|id| values.contains(id))
                    .map_or(term, word),
                _ => term,
            };
            let (mut left, mut right) = (root(left), root(right));
            if let (RelationTerm::Value { value: a, .. }, RelationTerm::Value { value: b, .. }) =
                (left, right)
            {
                if a > b {
                    std::mem::swap(&mut left, &mut right);
                }
            }
            premise = DifferencePremise::Compare {
                comparison: RelationComparison::NotEqual,
                left,
                right,
            };
        }
        if premises.contains(&premise) {
            return Ok(());
        }
        if premises.len() >= limits.max_constraints {
            return Err(DifferenceStop::Budget);
        }
        premises.push(premise);
        Ok(())
    };
    for &value in &values {
        push(DifferencePremise::Interval {
            value,
            interval: interval(state, word(value)).ok_or(DifferenceStop::InvalidInput)?,
        })?;
        if let Some(expression) = state.word_expression(value) {
            let right = match expression.root() {
                Some(root) if expression.scale() == 1 && values.contains(&root) => word(root),
                None if expression.is_constant() => RelationTerm::Constant(0),
                _ => continue,
            };
            if right != word(value) || expression.addend() != 0 {
                push(DifferencePremise::EqualOffset {
                    left: word(value),
                    right,
                    offset: i128::from(expression.addend()),
                })?;
            }
        }
    }
    for fact in facts {
        if let PathFact::Comparison {
            predicate,
            left,
            right,
        } = *fact
        {
            if values.contains(&left) && values.contains(&right) {
                let (comparison, left, right) = match predicate {
                    VirIntegerPredicate::Equal => (RelationComparison::Equal, left, right),
                    VirIntegerPredicate::NotEqual => (RelationComparison::NotEqual, left, right),
                    VirIntegerPredicate::LessThan => (RelationComparison::LessThan, left, right),
                    VirIntegerPredicate::LessOrEqual => {
                        (RelationComparison::LessOrEqual, left, right)
                    }
                    VirIntegerPredicate::GreaterThan => (RelationComparison::LessThan, right, left),
                    VirIntegerPredicate::GreaterOrEqual => {
                        (RelationComparison::LessOrEqual, right, left)
                    }
                };
                push(DifferencePremise::Compare {
                    comparison,
                    left: word(left),
                    right: word(right),
                })?;
            }
        }
    }
    for premise in relations {
        let (DifferencePremise::Bound { left, right, .. }
        | DifferencePremise::Compare { left, right, .. }) = premise
        else {
            continue;
        };
        if [left, right].into_iter().all(|term| match term {
            RelationTerm::Value { value, .. } => values.contains(&value),
            RelationTerm::Constant(_) => true,
            _ => false,
        }) {
            push(premise)?;
        }
    }
    Ok(premises)
}

pub(in crate::verifier) fn compare(
    state: &ResourceState,
    comparison: RelationComparison,
    left: RelationTerm,
    right: RelationTerm,
    limits: DifferenceLimits,
) -> (ObligationStatus, Option<DifferenceEvidence>) {
    let (status, evidence, _) = compare_observed(state, comparison, left, right, limits);
    (status, evidence)
}

pub(super) fn compare_observed(
    state: &ResourceState,
    comparison: RelationComparison,
    left: RelationTerm,
    right: RelationTerm,
    limits: DifferenceLimits,
) -> (
    ObligationStatus,
    Option<DifferenceEvidence>,
    Option<DifferenceStop>,
) {
    let (Some(a), Some(b)) = (interval(state, left), interval(state, right)) else {
        return (
            ObligationStatus::Unknown,
            None,
            Some(DifferenceStop::InvalidInput),
        );
    };
    let fast = match comparison {
        RelationComparison::LessThan => kernel::interval_lt_status(a, b),
        RelationComparison::LessOrEqual => kernel::interval_le_status(a, b),
        RelationComparison::Equal | RelationComparison::NotEqual => ObligationStatus::Unknown,
    };
    if fast != ObligationStatus::Unknown {
        return (fast, None, None);
    }
    let goal = DifferenceGoal {
        comparison,
        left,
        right,
    };
    let premises = match project(state, goal, limits) {
        Ok(premises) => premises,
        Err(stop) => return (ObligationStatus::Unknown, None, Some(stop)),
    };
    let evidence = solve_difference(&premises, goal, limits);
    (evidence.status, Some(evidence), None)
}
