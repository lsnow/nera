use super::*;

/// A closed interval of possible unsigned values.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct U64Interval {
    lower: u64,
    upper: u64,
}

impl U64Interval {
    pub fn new(lower: u64, upper: u64) -> Result<Self, U64IntervalError> {
        if lower > upper {
            return Err(U64IntervalError { lower, upper });
        }
        Ok(Self { lower, upper })
    }

    #[must_use]
    pub const fn exact(value: u64) -> Self {
        Self {
            lower: value,
            upper: value,
        }
    }

    #[must_use]
    pub const fn unknown() -> Self {
        Self {
            lower: 0,
            upper: u64::MAX,
        }
    }

    #[must_use]
    pub const fn lower(self) -> u64 {
        self.lower
    }

    #[must_use]
    pub const fn upper(self) -> u64 {
        self.upper
    }

    #[must_use]
    pub const fn exact_value(self) -> Option<u64> {
        if self.lower == self.upper {
            Some(self.lower)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn contains(self, value: u64) -> bool {
        self.lower <= value && value <= self.upper
    }

    /// Least interval containing both inputs.
    #[must_use]
    pub fn join(self, other: Self) -> Self {
        Self {
            lower: if self.lower < other.lower {
                self.lower
            } else {
                other.lower
            },
            upper: if self.upper > other.upper {
                self.upper
            } else {
                other.upper
            },
        }
    }

    /// Standard interval widening used at cyclic CFG entries.
    ///
    /// A bound that moves outwards is replaced by the corresponding domain
    /// limit, making every ascending interval chain finite.
    #[must_use]
    pub const fn widen(self, next: Self) -> Self {
        Self {
            lower: if next.lower < self.lower {
                0
            } else {
                self.lower
            },
            upper: if next.upper > self.upper {
                u64::MAX
            } else {
                self.upper
            },
        }
    }

    /// Values satisfying both intervals, or `None` when they are disjoint.
    #[must_use]
    pub fn intersection(self, other: Self) -> Option<Self> {
        Self::new(self.lower.max(other.lower), self.upper.min(other.upper)).ok()
    }
}

/// Reversed bounds supplied to [`U64Interval::new`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct U64IntervalError {
    pub lower: u64,
    pub upper: u64,
}

impl fmt::Display for U64IntervalError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "invalid unsigned interval: lower bound {} exceeds upper bound {}",
            self.lower, self.upper
        )
    }
}

impl Error for U64IntervalError {}

/// A checked affine expression with at most two nonnegative variable terms.
///
/// This is deliberately smaller than a solver term language. It retains the
/// correlations needed by fixed-stride rows/columns while every unsupported or
/// potentially wrapping operation drops back to interval-only reasoning.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AffineExpression {
    pub(super) root: Option<VirValueId>,
    pub(super) scale: u64,
    pub(super) addend: u64,
    pub(super) second: Option<(VirValueId, u64)>,
}

impl AffineExpression {
    #[must_use]
    pub const fn identity(root: VirValueId) -> Self {
        Self {
            root: Some(root),
            scale: 1,
            addend: 0,
            second: None,
        }
    }

    #[must_use]
    pub const fn constant(value: u64) -> Self {
        Self {
            root: None,
            scale: 0,
            addend: value,
            second: None,
        }
    }

    #[must_use]
    /// Only a single-term expression has a root here; use `is_constant` to
    /// distinguish constants from sums whose single root is absent.
    pub const fn root(self) -> Option<VirValueId> {
        if self.second.is_none() {
            self.root
        } else {
            None
        }
    }

    /// A missing single root does not imply a constant: two-root expressions
    /// intentionally cannot enter the one-variable difference fast paths.
    pub const fn is_constant(self) -> bool {
        self.root.is_none()
    }

    pub const fn terms(self) -> [Option<(VirValueId, u64)>; 2] {
        [
            match self.root {
                Some(root) => Some((root, self.scale)),
                None => None,
            },
            self.second,
        ]
    }

    pub fn same_terms(self, other: Self) -> bool {
        self.terms() == other.terms()
    }

    fn from_terms(addend: u64, terms: impl IntoIterator<Item = (VirValueId, u64)>) -> Option<Self> {
        let mut result = Self::constant(addend);
        let mut merged = BTreeMap::<VirValueId, u64>::new();
        for (root, scale) in terms {
            if scale == 0 {
                continue;
            }
            let entry = merged.entry(root).or_default();
            *entry = entry.checked_add(scale)?;
            if merged.len() > 2 {
                return None;
            }
        }
        let mut terms = merged.into_iter();
        if let Some((root, scale)) = terms.next() {
            result.root = Some(root);
            result.scale = scale;
        }
        result.second = terms.next();
        Some(result)
    }

    pub(crate) fn cancel_common(self, other: Self) -> (Self, Self) {
        let mut left = self.terms();
        let mut right = other.terms();
        for a in left.iter_mut().flatten() {
            for b in right.iter_mut().flatten() {
                if a.0 == b.0 {
                    let common = a.1.min(b.1);
                    a.1 -= common;
                    b.1 -= common;
                }
            }
        }
        (
            Self::from_terms(self.addend, left.into_iter().flatten()).unwrap(),
            Self::from_terms(other.addend, right.into_iter().flatten()).unwrap(),
        )
    }

    pub(crate) fn without_root(self, root: VirValueId) -> Self {
        Self::from_terms(
            self.addend,
            self.terms()
                .into_iter()
                .flatten()
                .filter(|(id, _)| *id != root),
        )
        .unwrap()
    }

    pub(crate) fn interval(
        self,
        mut value: impl FnMut(VirValueId) -> Option<U64Interval>,
    ) -> Option<U64Interval> {
        let mut lower = self.addend;
        let mut upper = self.addend;
        for (id, scale) in self.terms().into_iter().flatten() {
            let interval = value(id)?;
            lower = lower.checked_add(interval.lower().checked_mul(scale)?)?;
            upper = upper.checked_add(interval.upper().checked_mul(scale)?)?;
        }
        U64Interval::new(lower, upper).ok()
    }

    #[must_use]
    pub const fn scale(self) -> u64 {
        self.scale
    }

    #[must_use]
    pub const fn addend(self) -> u64 {
        self.addend
    }

    #[must_use]
    pub fn checked_add(self, other: Self) -> Option<Self> {
        Self::from_terms(
            self.addend.checked_add(other.addend)?,
            self.terms().into_iter().chain(other.terms()).flatten(),
        )
    }

    #[must_use]
    pub fn checked_add_constant(self, value: u64) -> Option<Self> {
        self.addend
            .checked_add(value)
            .map(|addend| Self { addend, ..self })
    }

    /// Multiplies the expression without introducing wrapping semantics.
    #[must_use]
    pub fn checked_scale(self, factor: u64) -> Option<Self> {
        if factor == 0 {
            return Some(Self::constant(0));
        }
        Some(Self {
            root: self.root,
            scale: self.scale.checked_mul(factor)?,
            addend: self.addend.checked_mul(factor)?,
            second: match self.second {
                Some((id, scale)) => Some((id, scale.checked_mul(factor)?)),
                None => None,
            },
        })
    }

    #[must_use]
    pub fn guaranteed_alignment(self) -> GuaranteedAlignment {
        let divisor = self
            .terms()
            .into_iter()
            .flatten()
            .fold(self.addend, |bits, (_, scale)| bits | scale);
        let bytes = if divisor == 0 {
            1_u64 << 63
        } else {
            1_u64 << divisor.trailing_zeros()
        };
        GuaranteedAlignment::new(bytes).unwrap_or_else(|_| GuaranteedAlignment::one())
    }

    pub(super) fn rename_root(self, renames: &BTreeMap<VirValueId, VirValueId>) -> Option<Self> {
        let terms = self
            .terms()
            .into_iter()
            .flatten()
            .map(|(id, scale)| Some((*renames.get(&id)?, scale)))
            .collect::<Option<Vec<_>>>()?;
        Self::from_terms(self.addend, terms)
    }
}

/// One symbolic byte-range endpoint with its conservative numeric interval.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SymbolicRangeBound {
    expression: AffineExpression,
    interval: U64Interval,
}

impl SymbolicRangeBound {
    #[must_use]
    pub const fn new(expression: AffineExpression, interval: U64Interval) -> Self {
        Self {
            expression,
            interval,
        }
    }

    #[must_use]
    pub const fn constant(value: u64) -> Self {
        Self::new(AffineExpression::constant(value), U64Interval::exact(value))
    }

    #[must_use]
    pub const fn expression(self) -> AffineExpression {
        self.expression
    }

    #[must_use]
    pub const fn interval(self) -> U64Interval {
        self.interval
    }

    #[must_use]
    pub fn checked_add_constant(self, value: u64) -> Option<Self> {
        Some(Self {
            expression: self.expression.checked_add_constant(value)?,
            interval: U64Interval::new(
                self.interval.lower().checked_add(value)?,
                self.interval.upper().checked_add(value)?,
            )
            .ok()?,
        })
    }
}

/// Three-valued Boolean domain used by path-sensitive transfer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AbstractBool {
    True,
    False,
    Unknown,
}

/// A `u64` value known to have been read from one canonical enum tag.
/// Retaining the object identity lets CFG branch refinement update the
/// active-variant state without treating arbitrary integer comparisons as
/// representation proofs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EnumDiscriminantFact {
    pub(super) interval: U64Interval,
    pub(super) pointer: AbstractPointer,
    pub(super) access: VirMemoryAccess,
}

impl EnumDiscriminantFact {
    #[must_use]
    pub const fn new(
        interval: U64Interval,
        pointer: AbstractPointer,
        access: VirMemoryAccess,
    ) -> Self {
        Self {
            interval,
            pointer,
            access,
        }
    }

    #[must_use]
    pub const fn interval(self) -> U64Interval {
        self.interval
    }

    #[must_use]
    pub const fn pointer(self) -> AbstractPointer {
        self.pointer
    }

    #[must_use]
    pub const fn access(self) -> VirMemoryAccess {
        self.access
    }

    fn join(self, other: Self) -> Option<Self> {
        (self.access == other.access).then(|| Self {
            interval: self.interval.join(other.interval),
            pointer: self.pointer.join(other.pointer),
            access: self.access,
        })
    }

    fn widen(self, next: Self) -> Option<Self> {
        (self.access == next.access).then(|| Self {
            interval: self.interval.widen(next.interval),
            pointer: self.pointer.widen(next.pointer),
            access: self.access,
        })
    }
}

impl AbstractBool {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::True, Self::True) | (Self::False, Self::False)
        ) {
            self
        } else {
            Self::Unknown
        }
    }
}

/// Abstract value facts keyed by a typed VIR SSA value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AbstractValue {
    U64(U64Interval),
    EnumDiscriminant(EnumDiscriminantFact),
    Bool(AbstractBool),
    Pointer(AbstractPointer),
    Permission(AbstractPermission),
}

impl AbstractValue {
    pub(super) fn join(self, other: Self, value: VirValueId) -> Result<Self, ResourceJoinError> {
        match (self, other) {
            (Self::U64(left), Self::U64(right)) => Ok(Self::U64(left.join(right))),
            (Self::EnumDiscriminant(left), Self::EnumDiscriminant(right)) => {
                Ok(left.join(right).map_or_else(
                    || Self::U64(left.interval().join(right.interval())),
                    Self::EnumDiscriminant,
                ))
            }
            (Self::EnumDiscriminant(left), Self::U64(right))
            | (Self::U64(right), Self::EnumDiscriminant(left)) => {
                Ok(Self::U64(left.interval().join(right)))
            }
            (Self::Bool(left), Self::Bool(right)) => Ok(Self::Bool(left.join(right))),
            (Self::Pointer(left), Self::Pointer(right)) => Ok(Self::Pointer(left.join(right))),
            (Self::Permission(left), Self::Permission(right)) => {
                Ok(Self::Permission(left.join(right)))
            }
            _ => Err(ResourceJoinError::ValueKindMismatch { value }),
        }
    }

    pub(super) fn widen(self, next: Self, value: VirValueId) -> Result<Self, ResourceJoinError> {
        match (self, next) {
            (Self::U64(current), Self::U64(next)) => Ok(Self::U64(current.widen(next))),
            (Self::EnumDiscriminant(current), Self::EnumDiscriminant(next)) => {
                Ok(current.widen(next).map_or_else(
                    || Self::U64(current.interval().widen(next.interval())),
                    Self::EnumDiscriminant,
                ))
            }
            (Self::EnumDiscriminant(current), Self::U64(next)) => {
                Ok(Self::U64(current.interval().widen(next)))
            }
            (Self::U64(current), Self::EnumDiscriminant(next)) => {
                Ok(Self::U64(current.widen(next.interval())))
            }
            (Self::Bool(current), Self::Bool(next)) => Ok(Self::Bool(current.join(next))),
            (Self::Pointer(current), Self::Pointer(next)) => Ok(Self::Pointer(current.widen(next))),
            (Self::Permission(current), Self::Permission(next)) => {
                Ok(Self::Permission(current.join(next)))
            }
            _ => Err(ResourceJoinError::ValueKindMismatch { value }),
        }
    }
}
