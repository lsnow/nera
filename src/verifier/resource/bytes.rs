use super::*;

/// A half-open byte range `[start, end)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteRange {
    pub(super) start: u64,
    pub(super) end: u64,
}

impl ByteRange {
    pub fn new(start: u64, end: u64) -> Result<Self, ByteRangeError> {
        if start > end {
            return Err(ByteRangeError::Reversed { start, end });
        }
        Ok(Self { start, end })
    }

    pub fn from_start_and_length(start: u64, length: u64) -> Result<Self, ByteRangeError> {
        let end = start
            .checked_add(length)
            .ok_or(ByteRangeError::EndOverflow { start, length })?;
        Ok(Self { start, end })
    }

    #[must_use]
    pub const fn start(self) -> u64 {
        self.start
    }

    #[must_use]
    pub const fn end(self) -> u64 {
        self.end
    }

    #[must_use]
    pub const fn length(self) -> u64 {
        self.end - self.start
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.start <= other.start && other.end <= self.end
    }

    #[must_use]
    pub const fn overlaps(self, other: Self) -> bool {
        self.start < other.end && other.start < self.end
    }

    #[must_use]
    pub fn intersection(self, other: Self) -> Option<Self> {
        let start = self.start.max(other.start);
        let end = self.end.min(other.end);
        (start < end).then_some(Self { start, end })
    }
}

/// Invalid half-open range construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteRangeError {
    Reversed { start: u64, end: u64 },
    EndOverflow { start: u64, length: u64 },
}

impl fmt::Display for ByteRangeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reversed { start, end } => {
                write!(
                    formatter,
                    "invalid byte range [{start}, {end}): start exceeds end"
                )
            }
            Self::EndOverflow { start, length } => write!(
                formatter,
                "byte range starting at {start} with length {length} exceeds u64 address space"
            ),
        }
    }
}

impl Error for ByteRangeError {}

/// A canonical union of non-empty half-open byte ranges.
///
/// Ranges are sorted, disjoint and non-adjacent. Mutation preserves that
/// representation, so equality is semantic equality and remains deterministic.
/// Once the fixed range budget is exceeded, `is_precise()` becomes false and
/// retained ranges are only a sound subset of the definite facts.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ByteSet {
    ranges: Vec<ByteRange>,
    precision_lost: bool,
}

impl ByteSet {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            ranges: Vec::new(),
            precision_lost: false,
        }
    }

    #[must_use]
    pub fn single(range: ByteRange) -> Self {
        let mut result = Self::new();
        result.insert(range);
        result
    }

    #[must_use]
    pub fn ranges(&self) -> &[ByteRange] {
        &self.ranges
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    #[must_use]
    pub const fn is_precise(&self) -> bool {
        !self.precision_lost
    }

    pub fn insert(&mut self, range: ByteRange) {
        if range.is_empty() {
            return;
        }

        let mut merged = range;
        let mut output = Vec::with_capacity(self.ranges.len() + 1);
        let mut inserted = false;
        for current in self.ranges.drain(..) {
            if current.end < merged.start {
                output.push(current);
            } else if merged.end < current.start {
                if !inserted {
                    output.push(merged);
                    inserted = true;
                }
                output.push(current);
            } else {
                merged = ByteRange {
                    start: merged.start.min(current.start),
                    end: merged.end.max(current.end),
                };
            }
        }
        if !inserted {
            output.push(merged);
        }
        if output.len() > VERIFIER_BYTE_SET_MAX_RANGES {
            self.precision_lost = true;
            output.truncate(VERIFIER_BYTE_SET_MAX_RANGES);
        }
        self.ranges = output;
    }

    pub fn remove(&mut self, range: ByteRange) {
        if range.is_empty() {
            return;
        }

        let mut output = Vec::with_capacity(self.ranges.len() + 1);
        for current in self.ranges.drain(..) {
            if !current.overlaps(range) {
                output.push(current);
                continue;
            }
            if current.start < range.start {
                output.push(ByteRange {
                    start: current.start,
                    end: range.start.min(current.end),
                });
            }
            if range.end < current.end {
                output.push(ByteRange {
                    start: range.end.max(current.start),
                    end: current.end,
                });
            }
        }
        if output.len() > VERIFIER_BYTE_SET_MAX_RANGES {
            self.precision_lost = true;
            output.truncate(VERIFIER_BYTE_SET_MAX_RANGES);
        }
        self.ranges = output;
    }

    #[must_use]
    pub fn contains(&self, range: ByteRange) -> bool {
        range.is_empty() || self.ranges.iter().any(|known| known.contains(range))
    }

    #[must_use]
    pub fn intersection(&self, other: &Self) -> Self {
        let mut result = Self::new();
        let mut left_index = 0;
        let mut right_index = 0;
        while left_index < self.ranges.len() && right_index < other.ranges.len() {
            let left = self.ranges[left_index];
            let right = other.ranges[right_index];
            if let Some(overlap) = left.intersection(right) {
                result.insert(overlap);
            }
            if left.end < right.end {
                left_index += 1;
            } else {
                right_index += 1;
            }
        }
        result.precision_lost = self.precision_lost || other.precision_lost;
        if result.ranges.len() > VERIFIER_BYTE_SET_MAX_RANGES {
            result.precision_lost = true;
            result.ranges.truncate(VERIFIER_BYTE_SET_MAX_RANGES);
        }
        result
    }

    /// Canonical union. If either input or the merged result exceeded the
    /// precision budget, the returned set remains explicitly imprecise.
    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.precision_lost |= other.precision_lost;
        for range in &other.ranges {
            result.insert(*range);
        }
        result
    }

    #[must_use]
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.intersection(other).is_empty()
    }
}

/// Minimum power-of-two alignment known to hold.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GuaranteedAlignment(u64);

impl GuaranteedAlignment {
    pub fn new(bytes: u64) -> Result<Self, GuaranteedAlignmentError> {
        if bytes == 0 || !bytes.is_power_of_two() {
            return Err(GuaranteedAlignmentError { bytes });
        }
        Ok(Self(bytes))
    }

    #[must_use]
    pub const fn one() -> Self {
        Self(1)
    }

    #[must_use]
    pub const fn bytes(self) -> u64 {
        self.0
    }

    /// The weaker alignment guaranteed by both incoming paths.
    #[must_use]
    pub fn join(self, other: Self) -> Self {
        if self.0 < other.0 { self } else { other }
    }
}

/// Invalid non-power-of-two alignment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GuaranteedAlignmentError {
    pub bytes: u64,
}

impl fmt::Display for GuaranteedAlignmentError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "alignment {} is not a nonzero power of two",
            self.bytes
        )
    }
}

impl Error for GuaranteedAlignmentError {}

/// Exact, bounded-affine symbolic, or unknown permission byte range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AbstractByteRange {
    Exact(ByteRange),
    Symbolic {
        start: SymbolicRangeBound,
        end: SymbolicRangeBound,
    },
    Unknown,
}

/// Snapshot of an evaluated object/view selection. `range` is the actual
/// symbolic extent; `envelope` only bounds possible accesses conservatively.
/// Losing SSA symbols never turns the envelope into permission.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MemoryFootprint {
    pub provenance: AbstractProvenance,
    pub access: VirMemoryAccess,
    pub stride_bytes: u64,
    pub range: AbstractByteRange,
    pub envelope: ByteRange,
}

impl MemoryFootprint {
    pub(super) fn join(self, other: Self) -> Option<Self> {
        if self.access != other.access || self.stride_bytes != other.stride_bytes {
            return None;
        }
        Some(Self {
            provenance: self.provenance.join(other.provenance),
            range: self.range.join(other.range),
            envelope: ByteRange {
                start: self.envelope.start.min(other.envelope.start),
                end: self.envelope.end.max(other.envelope.end),
            },
            ..self
        })
    }
    pub(in crate::verifier) fn project(self, remapper: &ExpressionRemapper) -> Self {
        Self {
            range: remapper.range(self.range),
            ..self
        }
    }
}

impl AbstractByteRange {
    #[must_use]
    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Exact(left), Self::Exact(right))
                if left.start == right.start && left.end == right.end =>
            {
                Self::Exact(left)
            }
            (
                Self::Symbolic {
                    start: left_start,
                    end: left_end,
                },
                Self::Symbolic {
                    start: right_start,
                    end: right_end,
                },
            ) if left_start == right_start && left_end == right_end => Self::Symbolic {
                start: left_start,
                end: left_end,
            },
            _ => Self::Unknown,
        }
    }

    #[must_use]
    pub const fn definitely_covers(self, access: ByteRange) -> bool {
        match self {
            Self::Exact(range) => range.contains(access),
            Self::Symbolic { .. } | Self::Unknown => false,
        }
    }

    #[must_use]
    pub const fn bounds(self) -> Option<(SymbolicRangeBound, SymbolicRangeBound)> {
        match self {
            Self::Exact(range) => Some((
                SymbolicRangeBound::constant(range.start()),
                SymbolicRangeBound::constant(range.end()),
            )),
            Self::Symbolic { start, end } => Some((start, end)),
            Self::Unknown => None,
        }
    }

    #[must_use]
    pub fn from_bounds(start: SymbolicRangeBound, end: SymbolicRangeBound) -> Self {
        // A singleton interval is already an evaluated constant. Do not keep
        // an unnecessary SSA dependency that would be lost at a CFG edge.
        let start = start
            .interval()
            .exact_value()
            .map_or(start, SymbolicRangeBound::constant);
        let end = end
            .interval()
            .exact_value()
            .map_or(end, SymbolicRangeBound::constant);
        match (
            start.expression().root(),
            start.interval().exact_value(),
            end.expression().root(),
            end.interval().exact_value(),
        ) {
            (None, Some(start), None, Some(end)) => ByteRange::new(start, end)
                .map(Self::Exact)
                .unwrap_or(Self::Unknown),
            _ => Self::Symbolic { start, end },
        }
    }
}
