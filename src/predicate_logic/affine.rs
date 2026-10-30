//! Mathematical affine expressions shared by domain checks and pure facts.
//! A signed interval is not evidence of a valid machine-word result.
use super::*;
mod envelope;
mod preimage;
mod projection;
pub(crate) use envelope::positive_word_envelope;
pub(crate) use preimage::positive_affine_preimage;
pub(crate) use projection::positive_affine_projection;

/// Mathematical affine terms for premises and unproved domain queries. Unlike
/// `AffineValue`, these do not assert that fresh machine arithmetic is defined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LinearWord<A: Ord> {
    pub(crate) constant: i128,
    pub(crate) terms: BTreeMap<A, i128>,
    pub(crate) lower: i128,
    pub(crate) upper: i128,
}

impl<A: Ord + Clone> LinearWord<A> {
    pub(crate) fn from_word(word: &AffineValue<A>) -> Self {
        Self {
            constant: word.constant,
            terms: word.terms.clone(),
            lower: i128::from(word.lower),
            upper: i128::from(word.upper),
        }
    }

    pub(crate) fn exact(value: i128) -> Self {
        Self {
            constant: value,
            terms: BTreeMap::new(),
            lower: value,
            upper: value,
        }
    }

    pub(crate) fn combine(&self, other: &Self, subtract: bool) -> Result<Self, LogicError> {
        let sign = if subtract { -1 } else { 1 };
        let mut terms = self.terms.clone();
        for (atom, coefficient) in &other.terms {
            let entry = terms.entry(atom.clone()).or_default();
            *entry = entry
                .checked_add(coefficient.checked_mul(sign).ok_or(LogicError::Overflow)?)
                .ok_or(LogicError::Overflow)?;
        }
        terms.retain(|_, coefficient| *coefficient != 0);
        if terms.len() > MAX_LINEAR_TERMS {
            return Err(LogicError::Budget);
        }
        let constant = self
            .constant
            .checked_add(
                other
                    .constant
                    .checked_mul(sign)
                    .ok_or(LogicError::Overflow)?,
            )
            .ok_or(LogicError::Overflow)?;
        if terms.is_empty() {
            return Ok(Self::exact(constant));
        }
        let (lower, upper) = if subtract {
            (
                self.lower.checked_sub(other.upper),
                self.upper.checked_sub(other.lower),
            )
        } else {
            (
                self.lower.checked_add(other.lower),
                self.upper.checked_add(other.upper),
            )
        };
        Ok(Self {
            constant,
            terms,
            lower: lower.ok_or(LogicError::Overflow)?,
            upper: upper.ok_or(LogicError::Overflow)?,
        })
    }

    pub(crate) fn scale(&self, factor: u64) -> Result<Self, LogicError> {
        if factor == 0 {
            return Ok(Self::exact(0));
        }
        let factor = i128::from(factor);
        Ok(Self {
            constant: self
                .constant
                .checked_mul(factor)
                .ok_or(LogicError::Overflow)?,
            terms: self
                .terms
                .iter()
                .map(|(a, n)| {
                    Ok((
                        a.clone(),
                        n.checked_mul(factor).ok_or(LogicError::Overflow)?,
                    ))
                })
                .collect::<Result<_, LogicError>>()?,
            lower: self.lower.checked_mul(factor).ok_or(LogicError::Overflow)?,
            upper: self.upper.checked_mul(factor).ok_or(LogicError::Overflow)?,
        })
    }
}

impl<A: Ord> LinearWord<A> {
    pub(crate) fn into_word(self) -> Result<AffineValue<A>, LogicError> {
        if self.lower > self.upper {
            return Err(LogicError::Unproved);
        }
        Ok(AffineValue {
            constant: self.constant,
            terms: self.terms,
            lower: u64::try_from(self.lower).map_err(|_| LogicError::Overflow)?,
            upper: u64::try_from(self.upper).map_err(|_| LogicError::Overflow)?,
        })
    }
}
