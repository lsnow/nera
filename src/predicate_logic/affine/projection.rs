//! Necessary operand bounds of a bounded positive affine sum. No source,
//! initialized storage or machine-expression validity is established here.
use super::*;

/// Project lower <= constant + sum(coefficient * operand) <= upper onto
/// each input interval. Returned intervals contain every satisfying tuple;
/// their Cartesian product need not satisfy the original sum constraint.
/// Terms must denote distinct inputs and have positive coefficients.
pub(crate) fn positive_affine_projection(
    constant: u64,
    terms: &[(u64, u64, u64)],
    lower: u64,
    upper: u64,
    budget: &mut LogicBudget,
) -> Result<Vec<(u64, u64)>, LogicError> {
    budget.charge(1)?;
    if terms.len() > MAX_LINEAR_TERMS {
        return Err(LogicError::Budget);
    }
    if lower > upper || terms.iter().any(|(c, lo, hi)| *c == 0 || lo > hi) {
        return Err(LogicError::InvalidNode);
    }
    let mut minimum = constant;
    let mut maximum = constant;
    for &(coefficient, lo, hi) in terms {
        budget.charge(1)?;
        minimum = minimum
            .checked_add(lo.checked_mul(coefficient).ok_or(LogicError::Overflow)?)
            .ok_or(LogicError::Overflow)?;
        maximum = maximum.saturating_add(hi.saturating_mul(coefficient));
    }
    if minimum > upper || maximum < lower {
        return Err(LogicError::Unproved);
    }
    let mut result = Vec::with_capacity(terms.len());
    for (index, &(coefficient, lo, hi)) in terms.iter().enumerate() {
        // The minimum was checked above, so this product/subtraction is exact.
        let other_min = minimum - lo * coefficient;
        let mut other_max = constant;
        for (other, &(c, _, high)) in terms.iter().enumerate() {
            budget.charge(1)?;
            if other != index {
                other_max = other_max.saturating_add(c.saturating_mul(high));
            }
        }
        let (low, high) = positive_affine_preimage(
            coefficient,
            0,
            lower.saturating_sub(other_max),
            upper - other_min,
            budget,
        )?;
        let bounds = (lo.max(low), hi.min(high));
        if bounds.0 > bounds.1 {
            return Err(LogicError::Unproved);
        }
        result.push(bounds);
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn projection_uses_other_operands_and_preserves_every_small_solution() {
        for a in 1..=3 {
            for b in 1..=3 {
                for lower in 0..=12 {
                    for upper in lower..=12 {
                        let result = positive_affine_projection(
                            1,
                            &[(a, 0, 4), (b, 1, 3)],
                            lower,
                            upper,
                            &mut LogicBudget::default(),
                        );
                        for x in 0..=4 {
                            for y in 1..=3 {
                                let sum = 1 + a * x + b * y;
                                if lower <= sum && sum <= upper {
                                    let projected = result
                                        .as_ref()
                                        .expect("a satisfying tuple cannot be rejected");
                                    assert!(projected[0].0 <= x && x <= projected[0].1);
                                    assert!(projected[1].0 <= y && y <= projected[1].1);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn projection_does_not_claim_independent_bounds_prove_the_joint_constraint() {
        assert_eq!(
            positive_affine_projection(
                0,
                &[(1, 0, 10), (1, 0, 10)],
                0,
                3,
                &mut LogicBudget::default()
            ),
            Ok(vec![(0, 3), (0, 3)])
        );
        assert_eq!(
            positive_affine_projection(
                1,
                &[(2, 0, u64::MAX), (1, 1, 1)],
                0,
                5,
                &mut LogicBudget::default()
            ),
            Ok(vec![(0, 1), (1, 1)])
        );
        assert_eq!(
            positive_affine_projection(
                0,
                &[(1, 0, 10), (1, 0, 1)],
                5,
                6,
                &mut LogicBudget::default()
            ),
            Ok(vec![(4, 6), (0, 1)])
        );
        assert_eq!(
            positive_affine_projection(
                0,
                &[(u64::MAX, 0, u64::MAX), (1, 1, 1)],
                0,
                u64::MAX,
                &mut LogicBudget::default()
            ),
            Ok(vec![(0, 0), (1, 1)])
        );
    }

    #[test]
    fn invalid_infeasible_and_exhausted_projection_fails_closed() {
        for (constant, terms, lower, upper, error) in [
            (0, vec![(0, 0, 1)], 0, 1, LogicError::InvalidNode),
            (0, vec![(1, 2, 1)], 0, 1, LogicError::InvalidNode),
            (0, vec![], 2, 1, LogicError::InvalidNode),
            (3, vec![], 0, 2, LogicError::Unproved),
            (0, vec![(2, 0, 10), (2, 0, 0)], 3, 3, LogicError::Unproved),
            (
                1,
                vec![(1, u64::MAX, u64::MAX)],
                0,
                u64::MAX,
                LogicError::Overflow,
            ),
            (
                0,
                vec![(1, 0, 1); MAX_LINEAR_TERMS + 1],
                0,
                1,
                LogicError::Budget,
            ),
        ] {
            assert_eq!(
                positive_affine_projection(
                    constant,
                    &terms,
                    lower,
                    upper,
                    &mut LogicBudget::default()
                ),
                Err(error)
            );
        }
        let mut budget = LogicBudget::default();
        budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
        assert_eq!(
            positive_affine_projection(0, &[(1, 0, 1)], 0, 1, &mut budget),
            Err(LogicError::Budget)
        );
        assert_eq!(
            positive_affine_projection(1, &[], 1, 1, &mut LogicBudget::default()),
            Ok(vec![])
        );
    }
}
