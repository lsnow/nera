//! Integer preimages of a positive affine word map. No source identity,
//! runtime mutation or initialized-storage fact is produced by this arithmetic.
use super::*;

/// All unsigned x satisfying lower <= scale*x+offset <= upper. The caller
/// establishes that this is the actual expression and that the output bounds
/// hold. Division precedes multiplication, so even maximal coefficients work.
pub(crate) fn positive_affine_preimage(
    scale: u64,
    offset: u64,
    lower: u64,
    upper: u64,
    budget: &mut LogicBudget,
) -> Result<(u64, u64), LogicError> {
    budget.charge(1)?;
    if scale == 0 || lower > upper {
        return Err(LogicError::InvalidNode);
    }
    let high = upper.checked_sub(offset).ok_or(LogicError::Unproved)? / scale;
    let low = lower.saturating_sub(offset);
    let low = low / scale + u64::from(!low.is_multiple_of(scale));
    if low > high {
        return Err(LogicError::Unproved);
    }
    Ok((low, high))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preimages_round_inward_without_multiplication_or_wrapping() {
        for (scale, offset, lower, upper, expected) in [
            (1, 2, 2, 3, (0, 1)),
            (3, 1, 6, 11, (2, 3)),
            (2, 1, 0, 3, (0, 1)),
            (1, 0, u64::MAX, u64::MAX, (u64::MAX, u64::MAX)),
            (u64::MAX, 0, 1, u64::MAX, (1, 1)),
            (u64::MAX, u64::MAX, u64::MAX, u64::MAX, (0, 0)),
        ] {
            assert_eq!(
                positive_affine_preimage(scale, offset, lower, upper, &mut LogicBudget::default()),
                Ok(expected)
            );
        }
    }

    #[test]
    fn empty_integer_preimages_invalid_domains_and_budget_are_errors() {
        for (scale, offset, lower, upper, error) in [
            (2, 0, 3, 3, LogicError::Unproved),
            (1, 3, 0, 2, LogicError::Unproved),
            (0, 1, 1, 2, LogicError::InvalidNode),
            (1, 0, 3, 2, LogicError::InvalidNode),
        ] {
            assert_eq!(
                positive_affine_preimage(scale, offset, lower, upper, &mut LogicBudget::default()),
                Err(error)
            );
        }
        let mut budget = LogicBudget::default();
        budget.charge(MAX_SUBSTITUTION_NODES).unwrap();
        assert_eq!(
            positive_affine_preimage(1, 0, 0, 1, &mut budget),
            Err(LogicError::Budget)
        );
    }
}
