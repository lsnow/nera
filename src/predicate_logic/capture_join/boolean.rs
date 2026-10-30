//! Merge precision only after source alignment and full Boolean equivalence.
//! Retain a deterministic input expression and every named leaf; equivalence
//! does not allow an adapter to forget a missing or mismatched source.
use super::*;
use crate::predicate_logic::scalar_template::ScalarTemplate;

type NamedLeaf<A, R> = (ScalarTemplate<A>, LogicValue<A, R>, bool);

type Leaves<T, A, R> = BTreeMap<ScalarTemplate<A>, TypedLogicValue<T, A, R>>;

pub(super) fn merge_equivalent<T: Copy + Eq, A: Ord + Clone, R: Clone + Eq>(
    left: &TypedLogicValue<T, A, R>,
    right: &TypedLogicValue<T, A, R>,
    budget: &mut LogicBudget,
    widen: bool,
) -> Result<TypedLogicValue<T, A, R>, LogicError> {
    let a = shape(&left.value, budget)?;
    let b = shape(&right.value, budget)?;
    let left_leaves = collect(left, budget)?;
    let right_leaves = collect(right, budget)?;
    if left_leaves.keys().ne(right_leaves.keys())
        || !super::super::boolean_equivalence::equivalent(&a, &b, budget)?
    {
        return Err(LogicError::Unbound);
    }
    let mut merged = BTreeMap::new();
    for (key, value) in left_leaves {
        let other = right_leaves.get(&key).ok_or(LogicError::Unbound)?;
        merged.insert(key, value.merge_capture(other, budget, widen)?);
    }
    // Shape order ignores path precision, so join does not choose whichever
    // predecessor was visited first. Widening still uses old -> new bounds.
    let mut result = if a <= b { left.clone() } else { right.clone() };
    for leaf in result.value.capture_leaves_mut(budget)? {
        if matches!(leaf, LogicValue::Bool(Some(_))) {
            continue;
        }
        let (key, _, negated) = named_leaf(leaf, budget)?;
        let value = merged.get(&key).ok_or(LogicError::Unbound)?.value.clone();
        *leaf = if negated { value.bool_not() } else { value };
    }
    Ok(result)
}

fn shape<A: Ord + Clone, R>(
    value: &LogicValue<A, R>,
    budget: &mut LogicBudget,
) -> Result<ScalarTemplate<A>, LogicError> {
    ScalarTemplate::capture(value, &mut |atom, _, _| Ok(atom.clone()), budget)
}

fn named_leaf<A: Ord + Clone, R: Clone>(
    leaf: &LogicValue<A, R>,
    budget: &mut LogicBudget,
) -> Result<NamedLeaf<A, R>, LogicError> {
    let mut value = leaf.clone();
    let negated = match &mut value {
        LogicValue::BoolAtom { negated, .. } | LogicValue::BoolComparison { negated, .. } => {
            let old = *negated;
            *negated = false;
            old
        }
        _ => return Err(LogicError::Unbound),
    };
    Ok((shape(&value, budget)?, value, negated))
}

fn collect<T: Copy + Eq, A: Ord + Clone, R: Clone + Eq>(
    value: &TypedLogicValue<T, A, R>,
    budget: &mut LogicBudget,
) -> Result<Leaves<T, A, R>, LogicError> {
    let mut leaves = Leaves::new();
    for leaf in value.value.capture_leaves(budget)? {
        if matches!(leaf, LogicValue::Bool(Some(_))) {
            continue;
        }
        let (key, value, _) = named_leaf(leaf, budget)?;
        let value = TypedLogicValue {
            ty: LogicType::Bool,
            value,
        };
        let value = if let Some(previous) = leaves.get(&key) {
            // Repeated occurrences within one predecessor are hulled first;
            // they must not be mistaken for successive widening iterations.
            value.merge_capture(previous, budget, false)?
        } else {
            value
        };
        leaves.insert(key, value);
    }
    Ok(leaves)
}

#[cfg(test)]
mod tests;
