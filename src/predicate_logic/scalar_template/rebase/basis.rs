//! Bounded integer elimination over supplied identities. Rows retain an exact
//! certificate in source coordinates; no interval or compiler state is used.
//! Policy distinguishes independent induction inputs, alternative immutable
//! descriptions, and exact whole capture coordinates. Consumers establish the
//! identities; neither a basis choice nor matching bounds is such evidence.
use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum SourcePolicy {
    Independent,
    Alternatives,
    /// Immutable captures may already be a complete supplied coordinate. That
    /// identity does not require other live coordinates to be independent.
    ExactCapture,
}

struct Row<A: Ord, B: Ord> {
    constant: i128,
    atoms: BTreeMap<B, i128>,
    sources: BTreeMap<A, i128>,
}

fn add_scaled<K: Ord + Clone>(
    target: &mut BTreeMap<K, i128>,
    source: &BTreeMap<K, i128>,
    scale: i128,
    budget: &mut LogicBudget,
) -> Result<(), LogicError> {
    budget.charge(1 + source.len())?;
    for (key, coefficient) in source {
        let entry = target.entry(key.clone()).or_default();
        *entry = entry
            .checked_add(coefficient.checked_mul(scale).ok_or(LogicError::Overflow)?)
            .ok_or(LogicError::Overflow)?;
    }
    target.retain(|_, c| *c != 0);
    if target.len() > MAX_LINEAR_TERMS {
        return Err(LogicError::Budget);
    }
    Ok(())
}

fn quotient(a: i128, b: i128) -> Result<i128, LogicError> {
    if a.checked_rem(b).ok_or(LogicError::Overflow)? != 0 {
        return Err(LogicError::Unbound);
    }
    a.checked_div(b).ok_or(LogicError::Overflow)
}

type RebasedIdentity<A, B> = (i128, BTreeMap<A, i128>, BTreeMap<B, i128>);

/// Return a checked identity: target = constant + source weights + residual
/// atoms. Residuals still require actual leaf bindings from the adapter.
pub(super) fn rebase<A: Ord + Clone, B: Ord + Clone>(
    constant: i128,
    atoms: &BTreeMap<B, i128>,
    sources: &[(A, AffineValue<B>)],
    policy: SourcePolicy,
    budget: &mut LogicBudget,
) -> Result<RebasedIdentity<A, B>, LogicError> {
    let mut candidates = BTreeMap::new();
    for (key, source) in sources {
        budget.charge(1 + source.terms.len())?;
        // Do not introduce unrelated roots to rewrite a fixed parameter into
        // a changing one. Cancellation requiring absent roots is unsupported.
        if !source.terms.is_empty() && source.terms.keys().all(|atom| atoms.contains_key(atom)) {
            candidates.insert(key, source);
        }
    }
    if candidates.len() > MAX_LINEAR_TERMS {
        return Err(LogicError::Budget);
    }
    if policy == SourcePolicy::ExactCapture {
        // Prefer the actual whole value over an arbitrary equivalent basis:
        // x+y and 2*(x+y) may both have live slots which remain independently
        // usable after a CFG merge. Bounds never participate in this match.
        for (key, source) in &candidates {
            budget.charge(1 + source.terms.len() + atoms.len())?;
            if source.constant == constant && source.terms == *atoms {
                return Ok((0, BTreeMap::from([((*key).clone(), 1)]), BTreeMap::new()));
            }
        }
        // Without a complete identity, keep the original independent-basis
        // checks. Do not silently discard a dependent runtime coordinate.
    }
    // Sort by source key, not caller iteration order; pivots are sorted atoms.
    // No search over alternative bases, fractions, or numerical range matches.
    let mut basis = BTreeMap::<B, Row<A, B>>::new();
    'candidate: for (key, source) in candidates {
        let mut row = Row {
            constant: source.constant,
            atoms: source.terms.clone(),
            sources: BTreeMap::from([(key.clone(), 1)]),
        };
        for (pivot, established) in &basis {
            budget.charge(1)?;
            let Some(coefficient) = row.atoms.get(pivot).copied() else {
                continue;
            };
            let ratio = match quotient(coefficient, established.atoms[pivot]) {
                Ok(ratio) => ratio,
                Err(LogicError::Unbound) if policy == SourcePolicy::Alternatives => {
                    continue 'candidate;
                }
                Err(error) => return Err(error),
            };
            let negative = ratio.checked_neg().ok_or(LogicError::Overflow)?;
            row.constant = row
                .constant
                .checked_sub(
                    established
                        .constant
                        .checked_mul(ratio)
                        .ok_or(LogicError::Overflow)?,
                )
                .ok_or(LogicError::Overflow)?;
            add_scaled(&mut row.atoms, &established.atoms, negative, budget)?;
            add_scaled(&mut row.sources, &established.sources, negative, budget)?;
        }
        let Some(pivot) = row.atoms.first_key_value().map(|(atom, _)| atom.clone()) else {
            // Linearly dependent changing inputs do not identify independent
            // induction coordinates, even if their entry constants differ.
            if policy == SourcePolicy::Alternatives {
                continue;
            }
            return Err(LogicError::Unbound);
        };
        basis.insert(pivot, row);
    }

    let mut constant = constant;
    let mut residual = atoms.clone();
    let mut weights = BTreeMap::new();
    for (pivot, row) in &basis {
        budget.charge(1)?;
        let Some(coefficient) = residual.get(pivot).copied() else {
            continue;
        };
        let ratio = match quotient(coefficient, row.atoms[pivot]) {
            Ok(ratio) => ratio,
            // A residual atom may still have an actual atomic binding. Never
            // approximate a fraction or invent an inverse source coordinate.
            Err(LogicError::Unbound) => continue,
            Err(error) => return Err(error),
        };
        constant = constant
            .checked_sub(
                row.constant
                    .checked_mul(ratio)
                    .ok_or(LogicError::Overflow)?,
            )
            .ok_or(LogicError::Overflow)?;
        add_scaled(
            &mut residual,
            &row.atoms,
            ratio.checked_neg().ok_or(LogicError::Overflow)?,
            budget,
        )?;
        add_scaled(&mut weights, &row.sources, ratio, budget)?;
    }
    Ok((constant, weights, residual))
}
