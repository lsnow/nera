//! Non-wrapping U64 values. Affine identities are retained only after definedness
//! is established; no result is installed into ResourceState.
use super::*;
use crate::{AffineExpression, ObligationStatus, SymbolicRangeBound};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Number {
    pub interval: U64Interval,
    expression: Option<AffineExpression>,
}

impl Number {
    pub(super) fn exact(value: u64) -> Self {
        Self::new(
            U64Interval::exact(value),
            Some(AffineExpression::constant(value)),
        )
    }
    pub(super) fn new(interval: U64Interval, expression: Option<AffineExpression>) -> Self {
        Self {
            interval,
            expression: interval
                .exact_value()
                .map(AffineExpression::constant)
                .or(expression),
        }
    }
}

pub(super) fn not(value: AbstractBool) -> AbstractBool {
    match value {
        AbstractBool::True => AbstractBool::False,
        AbstractBool::False => AbstractBool::True,
        AbstractBool::Unknown => AbstractBool::Unknown,
    }
}

pub(super) fn le(
    a: Number,
    b: Number,
    values: SnapshotValues<'_>,
    budget: &mut VcQueryBudget,
) -> Option<AbstractBool> {
    if let (Some(ae), Some(be), SnapshotValues::State(state)) = (a.expression, b.expression, values)
    {
        budget.begin_query()?;
        budget.charge(1)?;
        return Some(
            match budget.relations.ordered(
                state,
                SymbolicRangeBound::new(ae, a.interval),
                SymbolicRangeBound::new(be, b.interval),
                budget.relation_limits,
            ) {
                ObligationStatus::Proven => AbstractBool::True,
                ObligationStatus::Refuted => AbstractBool::False,
                ObligationStatus::Unknown => AbstractBool::Unknown,
            },
        );
    }
    Some(if a.interval.upper() <= b.interval.lower() {
        AbstractBool::True
    } else if a.interval.lower() > b.interval.upper() {
        AbstractBool::False
    } else {
        AbstractBool::Unknown
    })
}

pub(super) fn equal(
    a: Number,
    b: Number,
    values: SnapshotValues<'_>,
    budget: &mut VcQueryBudget,
) -> Option<AbstractBool> {
    let forward = le(a, b, values, budget)?;
    if forward == AbstractBool::False {
        return Some(forward);
    }
    Some(eval_and([forward, le(b, a, values, budget)?].into_iter()))
}

/// Outer None is query/work exhaustion; Some(None) means arithmetic definedness
/// could not be established. Neither may be turned into a Boolean false.
pub(super) fn arithmetic(
    a: Number,
    b: Number,
    subtract: bool,
    values: SnapshotValues<'_>,
    budget: &mut VcQueryBudget,
) -> Option<Option<Number>> {
    if subtract {
        if le(b, a, values, budget)? != AbstractBool::True {
            return Some(None);
        }
        if a.expression.is_some() && a.expression == b.expression {
            return Some(Some(Number::exact(0)));
        }
        let interval = U64Interval::new(
            a.interval.lower().saturating_sub(b.interval.upper()),
            a.interval.upper().saturating_sub(b.interval.lower()),
        )
        .ok()?;
        // Negative affine coefficients are outside the current range kernel.
        return Some(Some(Number::new(interval, None)));
    }
    let Some(upper) = a.interval.upper().checked_add(b.interval.upper()) else {
        return Some(None);
    };
    let lower = a.interval.lower().checked_add(b.interval.lower())?;
    Some(Some(Number::new(
        U64Interval::new(lower, upper).ok()?,
        a.expression
            .zip(b.expression)
            .and_then(|(a, b)| a.checked_add(b)),
    )))
}

pub(super) fn scale(a: Number, stride: u64) -> Option<Number> {
    let lower = a.interval.lower().checked_mul(stride)?;
    let upper = a.interval.upper().checked_mul(stride)?;
    Some(Number::new(
        U64Interval::new(lower, upper).ok()?,
        a.expression.and_then(|a| a.checked_scale(stride)),
    ))
}

pub(super) fn range(
    [a, b, c, d]: [Number; 4],
    disjoint: bool,
    values: SnapshotValues<'_>,
    budget: &mut VcQueryBudget,
) -> Option<AbstractBool> {
    let left_valid = le(a, b, values, budget)?;
    if left_valid == AbstractBool::False {
        return Some(left_valid);
    }
    let right_valid = le(c, d, values, budget)?;
    if right_valid == AbstractBool::False {
        return Some(right_valid);
    }
    let relation = if disjoint {
        let mut result = AbstractBool::False;
        // Empty intervals are disjoint even when their endpoint is inside the
        // other interval. Empty containment still requires an in-bounds point.
        for (left, right, eq) in [(a, b, true), (c, d, true), (b, c, false), (d, a, false)] {
            let next = if eq {
                equal(left, right, values, budget)?
            } else {
                le(left, right, values, budget)?
            };
            result = eval_or([result, next].into_iter());
            if result == AbstractBool::True {
                break;
            }
        }
        result
    } else {
        let start = le(a, c, values, budget)?;
        if start == AbstractBool::False {
            start
        } else {
            eval_and([start, le(d, b, values, budget)?].into_iter())
        }
    };
    Some(eval_and([left_valid, right_valid, relation].into_iter()))
}
