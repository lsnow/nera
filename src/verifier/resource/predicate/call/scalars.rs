//! Explicit value transport; no pure constraint is used to invent an ABI slot.
use super::*;
use crate::predicate_logic::LogicBudget;

pub(super) fn copy_scalars(
    source: &ResourceState,
    destination: &mut ResourceState,
    pairs: &[(VirValueId, VirValueId)],
    histories: &mut ScalarOriginTransport,
    budget: &mut LogicBudget,
) -> Result<(), PredicateError> {
    if pairs.len() > MAX_PREDICATE_LOCAL_ALIASES {
        return Err(PredicateError::Budget);
    }
    let mut targets = BTreeSet::new();
    for &(value, target) in pairs {
        budget.charge(1).map_err(logic::map_error)?;
        if !targets.insert(target) || destination.value(target).is_some() {
            return Err(PredicateError::InvalidBinding);
        }
        if !matches!(
            source.value(value),
            Some(AbstractValue::U64(_) | AbstractValue::Bool(_))
        ) {
            return Err(PredicateError::InvalidBinding);
        }
    }
    for &(value, target) in pairs {
        destination
            .define_value(target, *source.value(value).unwrap())
            .map_err(|_| PredicateError::InvalidBinding)?;
        histories
            .scalar(source, value, destination, target, budget)
            .map_err(logic::map_error)?;
    }
    // Preserve only expressions whose actual operands also travel through this
    // ABI. Unmapped inputs and scalar path assumptions stay in the source frame.
    let remapper = ExpressionRemapper::new(source, pairs);
    let mut first_target = BTreeMap::new();
    for &(value, target) in pairs {
        let canonical = *first_target.entry(value).or_insert(target);
        if let Some(expression) = source.word_expression(value)
            && let Some(expression) = remapper.expression(expression)
        {
            destination.word_expressions.insert(target, expression);
        } else if target != canonical && matches!(source.value(value), Some(AbstractValue::U64(_)))
        {
            destination
                .word_expressions
                .insert(target, AffineExpression::identity(canonical));
        }
    }
    Ok(())
}
