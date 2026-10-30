//! Join precision for already aligned immutable capture expressions.
//! Symbols are supplied by an adapter: this module cannot align CFG slots,
//! establish aliasing, choose new binders or grant resource authority.
use super::*;
mod boolean;

impl<T: Copy + Eq, A: Ord + Clone, R: Clone + Eq> TypedLogicValue<T, A, R> {
    /// Equivalent supported Boolean forms or the same scalar shape, with
    /// bounds covering both inputs. Distinct literals and anonymous unknowns
    /// cannot acquire a public parameter identity.
    pub(crate) fn join_capture(
        &self,
        other: &Self,
        budget: &mut LogicBudget,
    ) -> Result<Self, LogicError> {
        self.merge_normalized_capture(other, budget, false)
    }

    /// Accelerate growing captured bounds as well as ordinary runtime bounds.
    /// This preserves aligned shapes and covers both operands even when the
    /// caller has not yet made its successor ascending.
    pub(crate) fn widen_capture(
        &self,
        other: &Self,
        budget: &mut LogicBudget,
    ) -> Result<Self, LogicError> {
        self.merge_normalized_capture(other, budget, true)
    }

    fn merge_normalized_capture(
        &self,
        other: &Self,
        budget: &mut LogicBudget,
        widen: bool,
    ) -> Result<Self, LogicError> {
        if self.ty != other.ty {
            return Err(LogicError::TypeMismatch);
        }
        if self.ty == LogicType::Bool {
            let left = Self {
                ty: self.ty,
                value: self.value.canonical_boolean_capture(budget)?,
            };
            let right = Self {
                ty: other.ty,
                value: other.value.canonical_boolean_capture(budget)?,
            };
            match left.merge_capture(&right, budget, widen) {
                Err(LogicError::Unbound) => boolean::merge_equivalent(&left, &right, budget, widen),
                result => result,
            }
        } else {
            self.merge_capture(other, budget, widen)
        }
    }

    fn merge_capture(
        &self,
        other: &Self,
        budget: &mut LogicBudget,
        widen: bool,
    ) -> Result<Self, LogicError> {
        budget.charge(1)?;
        if self.ty != other.ty {
            return Err(LogicError::TypeMismatch);
        }
        let value = match (self.ty, &self.value, &other.value) {
            (
                LogicType::Bool,
                LogicValue::BoolBinary {
                    operation: a,
                    left: al,
                    right: ar,
                    negated: an,
                },
                LogicValue::BoolBinary {
                    operation: b,
                    left: bl,
                    right: br,
                    negated: bn,
                },
            ) if a == b && an == bn => {
                self.value.capture_leaves(budget)?;
                other.value.capture_leaves(budget)?;
                let mut merge = |left: &LogicValue<A, R>, right: &LogicValue<A, R>| {
                    Self {
                        ty: self.ty,
                        value: left.clone(),
                    }
                    .merge_capture(
                        &Self {
                            ty: self.ty,
                            value: right.clone(),
                        },
                        budget,
                        widen,
                    )
                    .map(|v| v.value)
                };
                let left = merge(al, bl)?;
                let right = merge(ar, br)?;
                LogicValue::boolean_binary(*a, left, right, *an, budget)?
            }
            (LogicType::U64 | LogicType::Usize, LogicValue::Word(a), LogicValue::Word(b)) => {
                LogicValue::Word(merge_word(a, b, budget, widen)?)
            }
            (LogicType::Bool, LogicValue::Bool(Some(a)), LogicValue::Bool(Some(b))) if a == b => {
                LogicValue::Bool(Some(*a))
            }
            (
                LogicType::Bool,
                LogicValue::BoolAtom {
                    atom: a,
                    negated: an,
                    known: ak,
                },
                LogicValue::BoolAtom {
                    atom: b,
                    negated: bn,
                    known: bk,
                },
            ) if a == b && an == bn => LogicValue::BoolAtom {
                atom: a.clone(),
                negated: *an,
                known: if ak == bk { *ak } else { None },
            },
            (
                LogicType::Bool,
                LogicValue::BoolComparison {
                    word_type: at,
                    comparison: a,
                    left: al,
                    right: ar,
                    negated: an,
                },
                LogicValue::BoolComparison {
                    word_type: bt,
                    comparison: b,
                    left: bl,
                    right: br,
                    negated: bn,
                },
            ) if at == bt && a == b && an == bn => LogicValue::BoolComparison {
                word_type: *at,
                comparison: *a,
                left: merge_word(al, bl, budget, widen)?,
                right: merge_word(ar, br, budget, widen)?,
                negated: *an,
            },
            (LogicType::Resource(_), LogicValue::Resource(a), LogicValue::Resource(b))
                if a == b =>
            {
                LogicValue::Resource(a.clone())
            }
            (
                LogicType::Resource(_),
                LogicValue::ResourceAtom { atom: a },
                LogicValue::ResourceAtom { atom: b },
            ) if a == b => LogicValue::ResourceAtom { atom: a.clone() },
            _ => return Err(LogicError::Unbound),
        };
        Ok(Self { ty: self.ty, value })
    }
}

fn merge_word<A: Ord + Clone>(
    a: &AffineValue<A>,
    b: &AffineValue<A>,
    budget: &mut LogicBudget,
    widen: bool,
) -> Result<AffineValue<A>, LogicError> {
    budget.charge(1 + a.terms.len() + b.terms.len())?;
    if a.terms.len() > MAX_LINEAR_TERMS || b.terms.len() > MAX_LINEAR_TERMS {
        return Err(LogicError::Budget);
    }
    if a.lower > a.upper || b.lower > b.upper {
        return Err(LogicError::InvalidNode);
    }
    if a.constant != b.constant || a.terms != b.terms {
        return Err(LogicError::Unbound);
    }
    Ok(AffineValue {
        constant: a.constant,
        terms: a.terms.clone(),
        lower: if widen && b.lower < a.lower {
            0
        } else {
            a.lower.min(b.lower)
        },
        upper: if widen && b.upper > a.upper {
            u64::MAX
        } else {
            a.upper.max(b.upper)
        },
    })
}

#[cfg(test)]
mod tests;
