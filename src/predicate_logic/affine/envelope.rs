//! Conservative bounds for an already established nonnegative word expression.
//! These bounds do not prove that evaluating machine arithmetic is defined.
use super::*;

pub(crate) fn positive_word_envelope(
    constant: u64,
    terms: impl IntoIterator<Item = (u64, u64, u64)>,
) -> Result<(u64, u64), LogicError> {
    let mut lower = constant;
    let mut upper = constant;
    for (index, (coefficient, low, high)) in terms.into_iter().enumerate() {
        if index >= MAX_LINEAR_TERMS {
            return Err(LogicError::Budget);
        }
        if low > high {
            return Err(LogicError::InvalidNode);
        }
        lower = lower
            .checked_add(low.checked_mul(coefficient).ok_or(LogicError::Overflow)?)
            .ok_or(LogicError::Overflow)?;
        upper = upper.saturating_add(high.saturating_mul(coefficient));
    }
    Ok((lower, upper))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nonnegative_envelopes_check_lower_and_saturate_only_upper() {
        assert_eq!(
            positive_word_envelope(1, [(2, 1, 3), (3, 2, 4)]),
            Ok((9, 19))
        );
        assert_eq!(
            positive_word_envelope(1, [(2, 1, u64::MAX), (1, 2, 3)]),
            Ok((5, u64::MAX))
        );
        assert_eq!(
            positive_word_envelope(1, [(1, u64::MAX, u64::MAX)]),
            Err(LogicError::Overflow)
        );
        assert_eq!(
            positive_word_envelope(0, [(1, 2, 1)]),
            Err(LogicError::InvalidNode)
        );
        assert_eq!(
            positive_word_envelope(0, [(1, 0, 1); MAX_LINEAR_TERMS + 1]),
            Err(LogicError::Budget)
        );
    }
}
