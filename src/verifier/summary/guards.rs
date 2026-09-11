//! Closed-summary branch restrictions. Unknown feasibility keeps a complete
//! world; only the existing bounded relation kernel can rule a numeric guard out.
use super::*;
use crate::verifier::relation::difference::{DifferencePremise, word};
use crate::verifier::relation::{RelationComparison as C, RelationTerm};
use crate::verifier::{AbstractValue, PathFact, ResourceState};

pub(super) fn restrict(
    guards: &[SummaryGuard],
    cx: &CallInstantiation<'_>,
) -> Option<ResourceState> {
    let mut state = cx.consumed.clone();
    for guard in guards {
        match guard {
            SummaryGuard::Boolean {
                parameter,
                expected,
            } => {
                let id = *cx.arguments.get(*parameter)?;
                let AbstractValue::Bool(value) = *state.value(id)? else {
                    return None;
                };
                if matches!(
                    (value, expected),
                    (AbstractBool::True, false) | (AbstractBool::False, true)
                ) {
                    return Some(ResourceState::unreachable());
                }
                state.conjoin_path_fact(PathFact::boolean(id, *expected));
                *state.value_mut(id)? = AbstractValue::Bool(if *expected {
                    AbstractBool::True
                } else {
                    AbstractBool::False
                });
            }
            SummaryGuard::Compare {
                predicate,
                left,
                right,
            } => {
                let term = |t: &ScalarTerm| match t {
                    ScalarTerm::Constant(n) => Some(RelationTerm::Constant(*n)),
                    ScalarTerm::Input(i) => Some(word(*cx.arguments.get(*i)?)),
                };
                let (left, right) = (term(left)?, term(right)?);
                let (comparison, left, right) = match predicate {
                    crate::VirIntegerPredicate::Equal => (C::Equal, left, right),
                    crate::VirIntegerPredicate::NotEqual => (C::NotEqual, left, right),
                    crate::VirIntegerPredicate::LessThan => (C::LessThan, left, right),
                    crate::VirIntegerPredicate::LessOrEqual => (C::LessOrEqual, left, right),
                    crate::VirIntegerPredicate::GreaterThan => (C::LessThan, right, left),
                    crate::VirIntegerPredicate::GreaterOrEqual => (C::LessOrEqual, right, left),
                };
                if cx
                    .queries
                    .compare(&state, comparison, left, right, cx.limits)
                    == ObligationStatus::Refuted
                {
                    return Some(ResourceState::unreachable());
                }
                if let (
                    RelationTerm::Value { value: a, .. },
                    RelationTerm::Value { value: b, .. },
                ) = (left, right)
                {
                    let predicate = match comparison {
                        C::Equal => crate::VirIntegerPredicate::Equal,
                        C::NotEqual => crate::VirIntegerPredicate::NotEqual,
                        C::LessThan => crate::VirIntegerPredicate::LessThan,
                        C::LessOrEqual => crate::VirIntegerPredicate::LessOrEqual,
                    };
                    state.conjoin_path_fact(PathFact::comparison(predicate, a, b));
                }
                state.learn_relations(
                    &[DifferencePremise::Compare {
                        comparison,
                        left,
                        right,
                    }],
                    cx.limits,
                );
            }
        }
    }
    Some(state)
}
