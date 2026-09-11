use std::collections::{BTreeMap, BTreeSet, btree_map::Entry};
use std::error::Error;
use std::fmt;

use crate::{
    VirBorrowRegionId, VirIntegerPredicate, VirLoanId, VirLoanKind, VirMemoryAccess, VirRegionId,
    VirValueId, VirVariantId,
};

mod initialization;
mod instance;
use super::relation::{
    difference::{DifferenceLimits, DifferencePremise},
    state::RelationState,
};
use initialization::InitializationPrefixes;

/// Maximum number of disjoint definite byte ranges retained in one set.
///
/// Dropping ranges only loses proof precision: a byte absent from both
/// initialization sets is unknown rather than assumed initialized.
pub const VERIFIER_BYTE_SET_MAX_RANGES: usize = 4_096;

/// Maximum number of exact enum subobjects tracked in one allocation.
pub const VERIFIER_OBJECT_STATE_MAX_ENTRIES: usize = 1_024;

/// Maximum number of typed resource move paths retained in one allocation.
///
/// Exceeding the budget only replaces the requested path with `Unknown`; it
/// never creates an available owner.
pub const VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES: usize = 1_024;

/// Maximum number of active enum alternatives retained across a CFG join.
pub const VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES: usize = 256;

/// Maximum canonical allocation-relative offsets retained for one place.
pub const VERIFIER_OBJECT_OFFSET_MAX_CANDIDATES: usize = 256;

/// Maximum number of live or maybe-live loans retained in one resource case.
pub const VERIFIER_MAX_ACTIVE_LOANS_PER_CASE: usize = 256;

/// Maximum number of available shared-reference authorities for one loan.
pub const VERIFIER_MAX_ALIASES_PER_LOAN: usize = 256;

/// Maximum parent chain followed while validating one reborrow transfer.
pub const VERIFIER_MAX_REBORROW_DEPTH: usize = 64;

/// Maximum region constraints consulted for one function analysis.
pub const VERIFIER_MAX_REGION_CONSTRAINTS_PER_FUNCTION: usize = 4_096;

/// Function-analysis-local allocation slot (not a concrete execution instance).
///
/// Transfer assigns these identities; they are never reconstructed from a
/// runtime integer address. Reusing a slot must go through the fresh-instance
/// transition, which forgets every old alias and preserves outstanding owners.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AbstractAllocationId {
    /// Identity introduced by an entry environment, contract or test fixture.
    External(u32),
    /// Identity of one allocation instruction in the current VIR function.
    VirAllocationSite(VirValueId),
    /// Identity of one function-local storage site. This namespace is
    /// deliberately disjoint from heap allocation sites even when the result
    /// value IDs are numerically equal.
    VirLocalStorageSite(VirValueId),
    /// Static slot for an existential resource produced by one call site.
    ///
    /// Distinct static call sites get distinct slots. Repeated execution at
    /// one site must use the fresh-instance transition, never blind replacement.
    ContractInstance { call_site: u64, resource: u32 },
    /// Fresh existential introduced by a closed body summary, not a contract slot.
    SummaryInstance { call_site: u64, resource: u32 },
    /// Symbolic owner stored in an ownership-bearing aggregate parameter.
    AbiEntryPayload {
        function: u32,
        parameter: u32,
        leaf: u32,
    },
    /// Existential owner produced in an ownership-bearing aggregate result.
    AbiCallPayload {
        call_site: u64,
        result: u32,
        leaf: u32,
    },
}

impl AbstractAllocationId {
    /// Creates an identity outside the local VIR allocation-site namespace.
    #[must_use]
    pub const fn new(raw: u32) -> Self {
        Self::External(raw)
    }

    #[must_use]
    pub const fn vir_allocation_site(value: VirValueId) -> Self {
        Self::VirAllocationSite(value)
    }

    #[must_use]
    pub const fn vir_local_storage_site(value: VirValueId) -> Self {
        Self::VirLocalStorageSite(value)
    }

    #[must_use]
    pub const fn contract_instance(call_site: u64, resource: u32) -> Self {
        Self::ContractInstance {
            call_site,
            resource,
        }
    }

    #[must_use]
    pub const fn abi_entry_payload(function: u32, parameter: u32, leaf: u32) -> Self {
        Self::AbiEntryPayload {
            function,
            parameter,
            leaf,
        }
    }

    #[must_use]
    pub const fn abi_call_payload(call_site: u64, result: u32, leaf: u32) -> Self {
        Self::AbiCallPayload {
            call_site,
            result,
            leaf,
        }
    }

    /// Returns the underlying external ID or VIR value ID.
    ///
    /// The namespace remains part of equality; equal raw values from different
    /// namespaces are deliberately distinct.
    #[must_use]
    pub const fn get(self) -> u32 {
        match self {
            Self::External(raw) => raw,
            Self::VirAllocationSite(value) => value.get(),
            Self::VirLocalStorageSite(value) => value.get(),
            Self::ContractInstance { resource, .. } => resource,
            Self::SummaryInstance { resource, .. } => resource,
            Self::AbiEntryPayload { leaf, .. } | Self::AbiCallPayload { leaf, .. } => leaf,
        }
    }

    const fn same_identity(self, other: Self) -> bool {
        match (self, other) {
            (
                Self::SummaryInstance {
                    call_site: a,
                    resource: x,
                },
                Self::SummaryInstance {
                    call_site: b,
                    resource: y,
                },
            ) => a == b && x == y,
            (Self::External(left), Self::External(right)) => left == right,
            (Self::VirAllocationSite(left), Self::VirAllocationSite(right)) => {
                left.get() == right.get()
            }
            (Self::VirLocalStorageSite(left), Self::VirLocalStorageSite(right)) => {
                left.get() == right.get()
            }
            (
                Self::ContractInstance {
                    call_site: left_site,
                    resource: left_resource,
                },
                Self::ContractInstance {
                    call_site: right_site,
                    resource: right_resource,
                },
            ) => left_site == right_site && left_resource == right_resource,
            (
                Self::AbiEntryPayload {
                    function: left_function,
                    parameter: left_parameter,
                    leaf: left_leaf,
                },
                Self::AbiEntryPayload {
                    function: right_function,
                    parameter: right_parameter,
                    leaf: right_leaf,
                },
            ) => {
                left_function == right_function
                    && left_parameter == right_parameter
                    && left_leaf == right_leaf
            }
            (
                Self::AbiCallPayload {
                    call_site: left_site,
                    result: left_result,
                    leaf: left_leaf,
                },
                Self::AbiCallPayload {
                    call_site: right_site,
                    result: right_result,
                    leaf: right_leaf,
                },
            ) => left_site == right_site && left_result == right_result && left_leaf == right_leaf,
            _ => false,
        }
    }
}

impl fmt::Display for AbstractAllocationId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::External(raw) => write!(formatter, "external:{raw}"),
            Self::SummaryInstance {
                call_site,
                resource,
            } => write!(formatter, "body-summary:{call_site}:{resource}"),
            Self::VirAllocationSite(value) => write!(formatter, "site:%{}", value.get()),
            Self::VirLocalStorageSite(value) => {
                write!(formatter, "local-storage:%{}", value.get())
            }
            Self::ContractInstance {
                call_site,
                resource,
            } => write!(formatter, "summary:{call_site}:{resource}"),
            Self::AbiEntryPayload {
                function,
                parameter,
                leaf,
            } => write!(formatter, "abi-entry:{function}:{parameter}:{leaf}"),
            Self::AbiCallPayload {
                call_site,
                result,
                leaf,
            } => write!(formatter, "abi-call:{call_site}:{result}:{leaf}"),
        }
    }
}

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
    root: Option<VirValueId>,
    scale: u64,
    addend: u64,
    second: Option<(VirValueId, u64)>,
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

    fn rename_root(self, renames: &BTreeMap<VirValueId, VirValueId>) -> Option<Self> {
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

/// A half-open byte range `[start, end)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteRange {
    start: u64,
    end: u64,
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

/// Liveness fact known at one program point.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LivenessState {
    Live,
    Dead,
    MaybeLive,
}

impl LivenessState {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Live, Self::Live) | (Self::Dead, Self::Dead)
        ) {
            self
        } else {
            Self::MaybeLive
        }
    }
}

/// Whether this abstract state definitely holds the allocation's free authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OwnershipState {
    Owned,
    Unowned,
    MaybeOwned,
}

impl OwnershipState {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Owned, Self::Owned) | (Self::Unowned, Self::Unowned)
        ) {
            self
        } else {
            Self::MaybeOwned
        }
    }
}

/// Classification of one complete byte range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InitializationClass {
    Initialized,
    Uninitialized,
    MaybeInitialized,
}

/// Definite initialized and definite uninitialized byte facts.
///
/// Bytes in neither set are unknown. The sets are always disjoint. Join uses
/// intersection for both sets, retaining only facts true on every path.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct InitializationState {
    initialized: ByteSet,
    uninitialized: ByteSet,
}

impl InitializationState {
    #[must_use]
    pub fn all_uninitialized(size_bytes: u64) -> Self {
        Self {
            initialized: ByteSet::new(),
            uninitialized: ByteSet::single(ByteRange {
                start: 0,
                end: size_bytes,
            }),
        }
    }

    #[must_use]
    pub const fn unknown() -> Self {
        Self {
            initialized: ByteSet::new(),
            uninitialized: ByteSet::new(),
        }
    }

    #[must_use]
    pub const fn initialized(&self) -> &ByteSet {
        &self.initialized
    }

    #[must_use]
    pub const fn uninitialized(&self) -> &ByteSet {
        &self.uninitialized
    }

    #[must_use]
    pub fn classify(&self, range: ByteRange) -> InitializationClass {
        if self.initialized.contains(range) {
            InitializationClass::Initialized
        } else if self.uninitialized.contains(range) {
            InitializationClass::Uninitialized
        } else {
            InitializationClass::MaybeInitialized
        }
    }

    fn mark_initialized(&mut self, range: ByteRange) {
        self.uninitialized.remove(range);
        self.initialized.insert(range);
    }

    fn mark_uninitialized(&mut self, range: ByteRange) {
        self.initialized.remove(range);
        self.uninitialized.insert(range);
    }

    fn forget(&mut self, range: ByteRange) {
        self.initialized.remove(range);
        self.uninitialized.remove(range);
    }

    fn forget_uninitialized(&mut self, range: ByteRange) {
        self.uninitialized.remove(range);
    }

    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        Self {
            initialized: self.initialized.intersection(&other.initialized),
            uninitialized: self.uninitialized.intersection(&other.uninitialized),
        }
    }
}

/// Exact location of one enum subobject inside an abstract allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ObjectStateKey {
    offset_bytes: u64,
    access: VirMemoryAccess,
}

/// Allocation-relative identity of one canonical resource leaf.
///
/// The physical byte offset makes the identity stable when the same leaf is
/// reached through a whole-object shape or through a projected field place.
/// `access` prevents overlapping enum representations with different pointer
/// types from being confused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ResourcePayloadKey {
    offset_bytes: u64,
    access: VirMemoryAccess,
}

impl ResourcePayloadKey {
    #[must_use]
    pub const fn new(offset_bytes: u64, access: VirMemoryAccess) -> Self {
        Self {
            offset_bytes,
            access,
        }
    }

    #[must_use]
    pub const fn offset_bytes(self) -> u64 {
        self.offset_bytes
    }

    #[must_use]
    pub const fn access(self) -> VirMemoryAccess {
        self.access
    }
}

/// Unforgeable logical value stored in one `Own<T>` memory leaf.
///
/// Pointer and permission facts form one atomic payload. They are never joined
/// independently because doing so could synthesize an owner that occurred on
/// no concrete path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypedResourcePayload {
    pointer: AbstractPointer,
    permission: AbstractPermission,
}

impl TypedResourcePayload {
    #[must_use]
    pub const fn new(pointer: AbstractPointer, permission: AbstractPermission) -> Self {
        Self {
            pointer,
            permission,
        }
    }

    #[must_use]
    pub const fn pointer(&self) -> AbstractPointer {
        self.pointer
    }

    #[must_use]
    pub const fn permission(&self) -> AbstractPermission {
        self.permission
    }
}

/// Availability of one canonical resource move path.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MovePathState {
    Available(Box<TypedResourcePayload>),
    Moved,
    Unknown,
}

impl MovePathState {
    #[must_use]
    pub fn available(payload: TypedResourcePayload) -> Self {
        Self::Available(Box::new(payload))
    }

    /// Atomic least upper bound. In particular, payload axes are not mixed.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Available(left), Self::Available(right)) if left == right => {
                Self::Available(left.clone())
            }
            (Self::Moved, Self::Moved) => Self::Moved,
            _ => Self::Unknown,
        }
    }
}

impl ObjectStateKey {
    #[must_use]
    pub const fn new(offset_bytes: u64, access: VirMemoryAccess) -> Self {
        Self {
            offset_bytes,
            access,
        }
    }

    #[must_use]
    pub const fn offset_bytes(self) -> u64 {
        self.offset_bytes
    }

    #[must_use]
    pub const fn access(self) -> VirMemoryAccess {
        self.access
    }
}

/// Path-sensitive knowledge of an enum subobject's active representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ActiveVariantState {
    Exact(VirVariantId),
    Alternatives(BTreeSet<VirVariantId>),
    Unknown,
}

impl ActiveVariantState {
    #[must_use]
    pub fn alternatives(&self) -> Option<BTreeSet<VirVariantId>> {
        match self {
            Self::Exact(variant) => Some(BTreeSet::from([*variant])),
            Self::Alternatives(variants) => Some(variants.clone()),
            Self::Unknown => None,
        }
    }

    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let (Some(mut variants), Some(other)) = (self.alternatives(), other.alternatives()) else {
            return Self::Unknown;
        };
        variants.extend(other);
        if variants.len() > VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES {
            Self::Unknown
        } else if variants.len() == 1 {
            Self::Exact(*variants.first().expect("one active variant"))
        } else {
            Self::Alternatives(variants)
        }
    }
}

/// Exact enum facts for subobjects whose allocation-relative address is known.
/// Missing entries have `Unknown` state.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ObjectState {
    active_variants: BTreeMap<ObjectStateKey, ActiveVariantState>,
    resource_payloads: BTreeMap<ResourcePayloadKey, MovePathState>,
    precision_lost: bool,
}

impl ObjectState {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            active_variants: BTreeMap::new(),
            resource_payloads: BTreeMap::new(),
            precision_lost: false,
        }
    }

    #[must_use]
    pub const fn active_variants(&self) -> &BTreeMap<ObjectStateKey, ActiveVariantState> {
        &self.active_variants
    }

    #[must_use]
    pub const fn resource_payloads(&self) -> &BTreeMap<ResourcePayloadKey, MovePathState> {
        &self.resource_payloads
    }

    #[must_use]
    pub const fn is_precise(&self) -> bool {
        !self.precision_lost
    }

    #[must_use]
    pub fn active_variant(&self, key: ObjectStateKey) -> ActiveVariantState {
        self.active_variants
            .get(&key)
            .cloned()
            .unwrap_or(ActiveVariantState::Unknown)
    }

    /// Records an exact fact. `false` means the fixed precision budget was
    /// exhausted and the requested subobject remains unknown.
    pub fn set_active_variant(&mut self, key: ObjectStateKey, state: ActiveVariantState) -> bool {
        if !self.active_variants.contains_key(&key)
            && self.active_variants.len() >= VERIFIER_OBJECT_STATE_MAX_ENTRIES
        {
            self.precision_lost = true;
            return false;
        }
        self.active_variants.insert(key, state);
        true
    }

    #[must_use]
    pub fn resource_payload(&self, key: ResourcePayloadKey) -> MovePathState {
        self.resource_payloads
            .get(&key)
            .cloned()
            .unwrap_or(MovePathState::Unknown)
    }

    /// Records one move path. `false` means the fixed precision budget was
    /// exhausted and the path remains conservatively unknown.
    pub fn set_resource_payload(&mut self, key: ResourcePayloadKey, state: MovePathState) -> bool {
        if !self.resource_payloads.contains_key(&key)
            && self.resource_payloads.len() >= VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES
        {
            self.precision_lost = true;
            return false;
        }
        self.resource_payloads.insert(key, state);
        true
    }

    pub fn forget_range(&mut self, range: ByteRange) {
        for (key, state) in &mut self.active_variants {
            if range.contains(ByteRange {
                start: key.offset_bytes,
                end: key.offset_bytes.saturating_add(1),
            }) {
                *state = ActiveVariantState::Unknown;
            }
        }
        for (key, state) in &mut self.resource_payloads {
            if range.contains(ByteRange {
                start: key.offset_bytes,
                end: key.offset_bytes.saturating_add(1),
            }) {
                *state = MovePathState::Unknown;
            }
        }
    }

    pub fn mark_resource_paths_moved(&mut self, range: ByteRange) {
        for (key, state) in &mut self.resource_payloads {
            if range.contains(ByteRange {
                start: key.offset_bytes,
                end: key.offset_bytes.saturating_add(1),
            }) {
                *state = MovePathState::Moved;
            }
        }
    }

    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        let mut joined = Self::new();
        joined.precision_lost = self.precision_lost || other.precision_lost;
        for (key, left) in &self.active_variants {
            let Some(right) = other.active_variants.get(key) else {
                continue;
            };
            let state = left.join(right);
            let inserted = joined.set_active_variant(*key, state);
            debug_assert!(inserted, "join cannot exceed either input's entry budget");
        }
        let resource_keys = self
            .resource_payloads
            .keys()
            .chain(other.resource_payloads.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        for key in resource_keys {
            let left = self.resource_payload(key);
            let right = other.resource_payload(key);
            let inserted = joined.set_resource_payload(key, left.join(&right));
            debug_assert!(inserted, "join cannot exceed the resource payload budget");
        }
        joined
    }

    fn project_cfg_edge(&self, remapper: &ExpressionRemapper) -> Self {
        let mut projected = self.clone();
        for state in projected.resource_payloads.values_mut() {
            if let MovePathState::Available(payload) = state {
                **payload = TypedResourcePayload::new(
                    remapper.pointer(payload.pointer()),
                    remapper.permission(payload.permission()),
                );
            }
        }
        projected
    }
}

/// An allocation's immutable shape and path-sensitive resource facts.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AbstractAllocation {
    region: Option<VirRegionId>,
    size_bytes: u64,
    alignment: GuaranteedAlignment,
    liveness: LivenessState,
    ownership: OwnershipState,
    initialization: InitializationState,
    valid_value_bytes: ByteSet,
    object_state: ObjectState,
    initialization_prefixes: InitializationPrefixes,
}

impl AbstractAllocation {
    pub fn new(
        region: VirRegionId,
        size_bytes: u64,
        alignment: u64,
    ) -> Result<Self, AbstractAllocationError> {
        Self::with_region(Some(region), size_bytes, alignment, OwnershipState::Owned)
    }

    /// Creates function-frame storage. It has no heap/contract region and no
    /// authority to outlive or free the current invocation.
    pub fn new_local(size_bytes: u64, alignment: u64) -> Result<Self, AbstractAllocationError> {
        Self::with_region(None, size_bytes, alignment, OwnershipState::Unowned)
    }

    fn with_region(
        region: Option<VirRegionId>,
        size_bytes: u64,
        alignment: u64,
        ownership: OwnershipState,
    ) -> Result<Self, AbstractAllocationError> {
        if size_bytes == 0 {
            return Err(AbstractAllocationError::ZeroSize);
        }
        let alignment = GuaranteedAlignment::new(alignment)
            .map_err(|error| AbstractAllocationError::InvalidAlignment(error.bytes))?;
        Ok(Self {
            region,
            size_bytes,
            alignment,
            liveness: LivenessState::Live,
            ownership,
            initialization: InitializationState::all_uninitialized(size_bytes),
            valid_value_bytes: ByteSet::new(),
            object_state: ObjectState::new(),
            initialization_prefixes: InitializationPrefixes::default(),
        })
    }

    #[must_use]
    pub const fn region(&self) -> Option<VirRegionId> {
        self.region
    }

    #[must_use]
    pub const fn size_bytes(&self) -> u64 {
        self.size_bytes
    }

    #[must_use]
    pub const fn alignment(&self) -> GuaranteedAlignment {
        self.alignment
    }

    #[must_use]
    pub const fn liveness(&self) -> LivenessState {
        self.liveness
    }

    #[must_use]
    pub const fn ownership(&self) -> OwnershipState {
        self.ownership
    }

    #[must_use]
    pub const fn initialization(&self) -> &InitializationState {
        &self.initialization
    }

    #[must_use]
    pub const fn valid_value_bytes(&self) -> &ByteSet {
        &self.valid_value_bytes
    }

    #[must_use]
    pub const fn object_state(&self) -> &ObjectState {
        &self.object_state
    }

    pub fn mark_dead(&mut self) {
        self.liveness = LivenessState::Dead;
        self.ownership = OwnershipState::Unowned;
    }

    pub fn set_liveness(&mut self, liveness: LivenessState) {
        self.liveness = liveness;
    }

    pub fn set_ownership(&mut self, ownership: OwnershipState) {
        self.ownership = ownership;
    }

    pub fn mark_initialized(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.initialization_prefixes.invalidate(range);
        self.initialization.mark_initialized(range);
        Ok(())
    }

    pub fn mark_valid(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.valid_value_bytes.insert(range);
        Ok(())
    }

    pub fn mark_uninitialized(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.initialization_prefixes.invalidate(range);
        self.initialization.mark_uninitialized(range);
        self.valid_value_bytes.remove(range);
        self.object_state.forget_range(range);
        self.object_state.mark_resource_paths_moved(range);
        Ok(())
    }

    pub fn forget_initialization(
        &mut self,
        range: ByteRange,
    ) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.initialization_prefixes.invalidate(range);
        self.initialization.forget(range);
        self.valid_value_bytes.remove(range);
        self.object_state.forget_range(range);
        Ok(())
    }

    pub fn forget_validity(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.initialization_prefixes.invalidate(range);
        self.valid_value_bytes.remove(range);
        Ok(())
    }

    #[must_use]
    pub fn active_variant(&self, key: ObjectStateKey) -> ActiveVariantState {
        self.object_state.active_variant(key)
    }

    pub fn set_active_variant(
        &mut self,
        key: ObjectStateKey,
        state: ActiveVariantState,
    ) -> Result<bool, AbstractAllocationError> {
        let range = ByteRange::from_start_and_length(key.offset_bytes(), 1).map_err(|_| {
            AbstractAllocationError::RangeOutOfBounds {
                range: ByteRange {
                    start: key.offset_bytes(),
                    end: u64::MAX,
                },
                size_bytes: self.size_bytes,
            }
        })?;
        self.check_range(range)?;
        Ok(self.object_state.set_active_variant(key, state))
    }

    #[must_use]
    pub fn resource_payload(&self, key: ResourcePayloadKey) -> MovePathState {
        self.object_state.resource_payload(key)
    }

    pub fn set_resource_payload(
        &mut self,
        key: ResourcePayloadKey,
        state: MovePathState,
    ) -> Result<bool, AbstractAllocationError> {
        let range = ByteRange::from_start_and_length(key.offset_bytes(), 1).map_err(|_| {
            AbstractAllocationError::RangeOutOfBounds {
                range: ByteRange {
                    start: key.offset_bytes(),
                    end: u64::MAX,
                },
                size_bytes: self.size_bytes,
            }
        })?;
        self.check_range(range)?;
        Ok(self.object_state.set_resource_payload(key, state))
    }

    pub fn forget_object_state(&mut self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.object_state.forget_range(range);
        Ok(())
    }

    /// Drops only the fact that bytes are definitely uninitialized.
    ///
    /// A write through an interval pointer may initialize any byte in its
    /// access envelope while preserving already-initialized bytes.
    pub fn forget_uninitialized(
        &mut self,
        range: ByteRange,
    ) -> Result<(), AbstractAllocationError> {
        self.check_range(range)?;
        self.initialization_prefixes.invalidate(range);
        self.initialization.forget_uninitialized(range);
        Ok(())
    }

    fn check_range(&self, range: ByteRange) -> Result<(), AbstractAllocationError> {
        if range.end > self.size_bytes {
            return Err(AbstractAllocationError::RangeOutOfBounds {
                range,
                size_bytes: self.size_bytes,
            });
        }
        Ok(())
    }

    fn join(&self, id: AbstractAllocationId, other: &Self) -> Result<Self, ResourceJoinError> {
        if self.region != other.region {
            return Err(ResourceJoinError::AllocationRegionMismatch { allocation: id });
        }
        if self.size_bytes != other.size_bytes {
            return Err(ResourceJoinError::AllocationSizeMismatch { allocation: id });
        }
        if self.alignment != other.alignment {
            return Err(ResourceJoinError::AllocationAlignmentMismatch { allocation: id });
        }
        Ok(Self {
            region: self.region,
            size_bytes: self.size_bytes,
            alignment: self.alignment,
            liveness: self.liveness.join(other.liveness),
            ownership: self.ownership.join(other.ownership),
            initialization: self.initialization.join(&other.initialization),
            valid_value_bytes: self
                .valid_value_bytes
                .intersection(&other.valid_value_bytes),
            object_state: self.object_state.join(&other.object_state),
            initialization_prefixes: self
                .initialization_prefixes
                .join(&other.initialization_prefixes),
        })
    }

    fn project_cfg_edge(
        &self,
        remapper: &ExpressionRemapper,
        values: &BTreeMap<VirValueId, AbstractValue>,
    ) -> Self {
        let mut projected = self.clone();
        projected.reduce_initialization_prefixes(values);
        projected.object_state = self.object_state.project_cfg_edge(remapper);
        projected.initialization_prefixes = self.initialization_prefixes.project(remapper, values);
        projected
    }
}

/// Invalid facts used to construct or update an abstract allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbstractAllocationError {
    ZeroSize,
    InvalidAlignment(u64),
    RangeOutOfBounds { range: ByteRange, size_bytes: u64 },
}

impl fmt::Display for AbstractAllocationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroSize => formatter.write_str("abstract allocation size must be nonzero"),
            Self::InvalidAlignment(alignment) => write!(
                formatter,
                "abstract allocation alignment {alignment} is not a nonzero power of two"
            ),
            Self::RangeOutOfBounds { range, size_bytes } => write!(
                formatter,
                "byte range [{}, {}) is outside allocation of {size_bytes} bytes",
                range.start, range.end
            ),
        }
    }
}

impl Error for AbstractAllocationError {}

/// Pointer provenance knowledge.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AbstractProvenance {
    Known(AbstractAllocationId),
    Unknown,
}

impl AbstractProvenance {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Known(left), Self::Known(right)) if left.same_identity(right) => {
                Self::Known(left)
            }
            _ => Self::Unknown,
        }
    }
}

/// Canonical allocation-relative object offsets represented by the analysis.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AbstractObjectOffsets {
    Exact(u64),
    Strided {
        first: u64,
        stride_bytes: u64,
        count: u16,
    },
    Unknown,
}

impl AbstractObjectOffsets {
    #[must_use]
    pub fn from_interval(interval: U64Interval) -> Self {
        interval.exact_value().map_or(Self::Unknown, Self::Exact)
    }

    #[must_use]
    pub fn candidates(self) -> Option<Vec<u64>> {
        match self {
            Self::Exact(offset) => Some(vec![offset]),
            Self::Strided {
                first,
                stride_bytes,
                count,
            } => (0..u64::from(count))
                .map(|index| index.checked_mul(stride_bytes)?.checked_add(first))
                .collect(),
            Self::Unknown => None,
        }
    }

    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Exact(left), Self::Exact(right)) if left == right => self,
            (Self::Exact(_), Self::Exact(_)) => Self::Unknown,
            (
                Self::Strided {
                    first: left_first,
                    stride_bytes: left_stride,
                    count: left_count,
                },
                Self::Strided {
                    first: right_first,
                    stride_bytes: right_stride,
                    count: right_count,
                },
            ) if left_first == right_first
                && left_stride == right_stride
                && left_count == right_count =>
            {
                self
            }
            _ => Self::Unknown,
        }
    }

    #[must_use]
    pub const fn offset_by_exact(self, delta: u64) -> Self {
        match self {
            Self::Exact(offset) => match offset.checked_add(delta) {
                Some(offset) => Self::Exact(offset),
                None => Self::Unknown,
            },
            Self::Strided {
                first,
                stride_bytes,
                count,
            } => match first.checked_add(delta) {
                Some(first) => Self::Strided {
                    first,
                    stride_bytes,
                    count,
                },
                None => Self::Unknown,
            },
            Self::Unknown => Self::Unknown,
        }
    }

    #[must_use]
    pub fn offset_by_index(self, indices: U64Interval, stride_bytes: u64) -> Self {
        let Some(count) = indices
            .upper()
            .checked_sub(indices.lower())
            .and_then(|width| width.checked_add(1))
            .and_then(|count| usize::try_from(count).ok())
        else {
            return Self::Unknown;
        };
        if count > VERIFIER_OBJECT_OFFSET_MAX_CANDIDATES {
            return Self::Unknown;
        }
        let Some(delta) = indices.lower().checked_mul(stride_bytes) else {
            return Self::Unknown;
        };
        let Self::Exact(base) = self else {
            return Self::Unknown;
        };
        let Some(first) = base.checked_add(delta) else {
            return Self::Unknown;
        };
        if count == 1 {
            Self::Exact(first)
        } else {
            Self::Strided {
                first,
                stride_bytes,
                count: u16::try_from(count).expect("candidate budget fits u16"),
            }
        }
    }
}

/// Abstract pointer value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AbstractPointer {
    provenance: AbstractProvenance,
    offset_bytes: U64Interval,
    alignment: GuaranteedAlignment,
    offset_expression: Option<AffineExpression>,
    access: Option<VirMemoryAccess>,
    object_offsets: AbstractObjectOffsets,
    /// Actual slice selection produced by address calculation, not authority.
    slice_footprint: Option<MemoryFootprint>,
    domain: crate::VirPointerDomain<AbstractByteRange>,
    paths: crate::VirPointerPaths,
}

impl AbstractPointer {
    #[must_use]
    pub const fn new(
        provenance: AbstractProvenance,
        offset_bytes: U64Interval,
        alignment: GuaranteedAlignment,
    ) -> Self {
        Self {
            provenance,
            offset_bytes,
            alignment,
            offset_expression: None,
            access: None,
            slice_footprint: None,
            domain: crate::VirPointerDomain::Allocation,
            paths: crate::VirPointerPaths {
                object: None,
                domain: None,
            },
            object_offsets: if offset_bytes.lower() == offset_bytes.upper() {
                AbstractObjectOffsets::Exact(offset_bytes.lower())
            } else {
                AbstractObjectOffsets::Unknown
            },
        }
    }

    #[must_use]
    pub const fn with_offset_expression(mut self, expression: Option<AffineExpression>) -> Self {
        self.offset_expression = expression;
        self
    }

    #[must_use]
    pub const fn with_memory_access(mut self, access: Option<VirMemoryAccess>) -> Self {
        if self.access.is_none()
            && let Some(access) = access
        {
            self.paths = crate::VirPointerPaths::root(access);
        }
        self.access = access;
        self
    }

    #[must_use]
    pub const fn with_object_offsets(mut self, object_offsets: AbstractObjectOffsets) -> Self {
        self.object_offsets = object_offsets;
        self
    }

    #[must_use]
    pub const fn provenance(self) -> AbstractProvenance {
        self.provenance
    }

    #[must_use]
    pub const fn offset_bytes(self) -> U64Interval {
        self.offset_bytes
    }

    #[must_use]
    pub const fn alignment(self) -> GuaranteedAlignment {
        self.alignment
    }

    #[must_use]
    pub const fn offset_expression(self) -> Option<AffineExpression> {
        self.offset_expression
    }

    #[must_use]
    pub const fn memory_access(self) -> Option<VirMemoryAccess> {
        self.access
    }

    #[must_use]
    pub const fn object_offsets(self) -> AbstractObjectOffsets {
        self.object_offsets
    }

    pub const fn slice_footprint(self) -> Option<MemoryFootprint> {
        self.slice_footprint
    }
    pub const fn domain(self) -> crate::VirPointerDomain<AbstractByteRange> {
        self.domain
    }
    pub const fn paths(self) -> crate::VirPointerPaths {
        self.paths
    }
    pub const fn with_paths(mut self, paths: crate::VirPointerPaths) -> Self {
        self.paths = paths;
        self
    }
    pub const fn with_domain(mut self, domain: crate::VirPointerDomain<AbstractByteRange>) -> Self {
        self.domain = domain;
        self
    }
    pub const fn with_slice_footprint(mut self, footprint: Option<MemoryFootprint>) -> Self {
        self.slice_footprint = footprint;
        self
    }

    #[must_use]
    pub fn join(self, other: Self) -> Self {
        Self {
            provenance: self.provenance.join(other.provenance),
            paths: self.paths.join(other.paths),
            domain: if self.domain == other.domain {
                self.domain
            } else {
                crate::VirPointerDomain::Unknown
            },
            offset_bytes: self.offset_bytes.join(other.offset_bytes),
            alignment: self.alignment.join(other.alignment),
            offset_expression: if self.offset_expression == other.offset_expression {
                self.offset_expression
            } else {
                None
            },
            access: if self.access == other.access {
                self.access
            } else {
                None
            },
            object_offsets: self.object_offsets.join(other.object_offsets),
            slice_footprint: match (self.slice_footprint, other.slice_footprint) {
                (Some(a), Some(b)) => a.join(b),
                _ => None,
            },
        }
    }

    #[must_use]
    fn widen(self, next: Self) -> Self {
        Self {
            provenance: self.provenance.join(next.provenance),
            paths: self.paths.join(next.paths),
            domain: if self.domain == next.domain {
                self.domain
            } else {
                crate::VirPointerDomain::Unknown
            },
            offset_bytes: self.offset_bytes.widen(next.offset_bytes),
            alignment: self.alignment.join(next.alignment),
            offset_expression: if self.offset_expression == next.offset_expression {
                self.offset_expression
            } else {
                None
            },
            access: if self.access == next.access {
                self.access
            } else {
                None
            },
            object_offsets: self.object_offsets.join(next.object_offsets),
            slice_footprint: match (self.slice_footprint, next.slice_footprint) {
                (Some(a), Some(b)) => a.join(b),
                _ => None,
            },
        }
    }
}

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
    fn join(self, other: Self) -> Option<Self> {
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
    fn project(self, remapper: &ExpressionRemapper) -> Self {
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
            start.expression.root(),
            start.interval.exact_value(),
            end.expression.root(),
            end.interval.exact_value(),
        ) {
            (None, Some(start), None, Some(end)) => ByteRange::new(start, end)
                .map(Self::Exact)
                .unwrap_or(Self::Unknown),
            _ => Self::Symbolic { start, end },
        }
    }
}

/// Access strength guaranteed by a permission token.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AccessPermission {
    /// The permission is definitely read-only.
    Read,
    /// The permission is definitely writable (and therefore readable).
    Write,
    /// Every represented permission is readable, but writability differs or
    /// is not known precisely enough.
    MaybeWrite,
}

impl AccessPermission {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Read, Self::Read)
                | (Self::Write, Self::Write)
                | (Self::MaybeWrite, Self::MaybeWrite)
        ) {
            self
        } else {
            Self::MaybeWrite
        }
    }
}

/// Whether a complete permission can release its allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FreeCapability {
    Yes,
    No,
    Maybe,
}

impl FreeCapability {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!((self, other), (Self::Yes, Self::Yes) | (Self::No, Self::No)) {
            self
        } else {
            Self::Maybe
        }
    }
}

/// Linear availability of one permission SSA value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PermissionAvailability {
    Available,
    Consumed,
    MaybeConsumed,
}

/// Semantic authority carried by one permission SSA value.
///
/// Authority is never reconstructed from pointer bits, provenance or range.
/// `Unknown` is the conservative join/budget result and grants no access by
/// itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PermissionAuthority {
    Owner,
    Loan(VirLoanId),
    Unknown,
}

impl PermissionAuthority {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Owner, Self::Owner) | (Self::Unknown, Self::Unknown)
        ) {
            self
        } else {
            match (self, other) {
                (Self::Loan(left), Self::Loan(right)) if left.get() == right.get() => self,
                _ => Self::Unknown,
            }
        }
    }
}

impl PermissionAvailability {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Available, Self::Available) | (Self::Consumed, Self::Consumed)
        ) {
            self
        } else {
            Self::MaybeConsumed
        }
    }
}

/// Abstract linear permission carried by a VIR `permission` value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AbstractPermission {
    provenance: AbstractProvenance,
    range: AbstractByteRange,
    access: AccessPermission,
    free: FreeCapability,
    availability: PermissionAvailability,
    authority: PermissionAuthority,
}

impl AbstractPermission {
    #[must_use]
    pub const fn new(
        provenance: AbstractProvenance,
        range: AbstractByteRange,
        access: AccessPermission,
        free: FreeCapability,
    ) -> Self {
        Self {
            provenance,
            range,
            access,
            free,
            availability: PermissionAvailability::Available,
            authority: PermissionAuthority::Owner,
        }
    }

    #[must_use]
    pub const fn provenance(self) -> AbstractProvenance {
        self.provenance
    }

    #[must_use]
    pub const fn range(self) -> AbstractByteRange {
        self.range
    }

    #[must_use]
    pub const fn access(self) -> AccessPermission {
        self.access
    }

    #[must_use]
    pub const fn free_capability(self) -> FreeCapability {
        self.free
    }

    #[must_use]
    pub const fn availability(self) -> PermissionAvailability {
        self.availability
    }

    #[must_use]
    pub const fn authority(self) -> PermissionAuthority {
        self.authority
    }

    #[must_use]
    pub const fn with_availability(mut self, availability: PermissionAvailability) -> Self {
        self.availability = availability;
        self
    }

    #[must_use]
    pub const fn with_authority(mut self, authority: PermissionAuthority) -> Self {
        self.authority = authority;
        self
    }

    pub fn mark_consumed(&mut self) {
        self.availability = PermissionAvailability::Consumed;
    }

    #[must_use]
    pub fn join(self, other: Self) -> Self {
        Self {
            provenance: self.provenance.join(other.provenance),
            range: self.range.join(other.range),
            access: self.access.join(other.access),
            free: self.free.join(other.free),
            availability: self.availability.join(other.availability),
            authority: self.authority.join(other.authority),
        }
    }
}

/// Path-local lifecycle of one canonical loan instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LoanActivity {
    Active,
    Suspended,
    Ended,
    /// At least one joined/budgeted alternative may still be active.
    MaybeActive,
}

impl LoanActivity {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Active, Self::Active)
                | (Self::Suspended, Self::Suspended)
                | (Self::Ended, Self::Ended)
                | (Self::MaybeActive, Self::MaybeActive)
        ) {
            self
        } else {
            Self::MaybeActive
        }
    }
}

/// Conservative precision losses specific to the loan domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LoanPrecisionLoss {
    ActiveLoanBudget,
    LoanAliasBudget,
    RegionConstraintBudget,
    ReborrowDepthBudget,
    LoanJoin,
    LoanLoopWidening,
}

/// One concrete carrier of a loan authority in the abstract state.
///
/// References normally travel in SSA permission values.  A reference-bearing
/// aggregate instead owns the authority at an exact typed payload location;
/// keeping both forms in the same set prevents an object move/copy from
/// manufacturing or losing an alias behind the verifier's back.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AbstractLoanAuthority {
    Value(VirValueId),
    Stored {
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    },
}

impl AbstractLoanAuthority {
    #[must_use]
    pub const fn value(value: VirValueId) -> Self {
        Self::Value(value)
    }

    #[must_use]
    pub const fn stored(allocation: AbstractAllocationId, payload: ResourcePayloadKey) -> Self {
        Self::Stored {
            allocation,
            payload,
        }
    }
}

/// Canonical abstract loan fact stored atomically with all resource facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbstractLoan {
    provenance: AbstractProvenance,
    range: ByteRange,
    footprint: Option<MemoryFootprint>,
    kind: VirLoanKind,
    region: VirBorrowRegionId,
    parent: Option<VirLoanId>,
    activity: LoanActivity,
    authorities: BTreeSet<AbstractLoanAuthority>,
}

impl AbstractLoan {
    #[must_use]
    pub const fn new(
        provenance: AbstractProvenance,
        range: ByteRange,
        kind: VirLoanKind,
        region: VirBorrowRegionId,
        parent: Option<VirLoanId>,
        activity: LoanActivity,
    ) -> Self {
        Self {
            provenance,
            range,
            footprint: None,
            kind,
            region,
            parent,
            activity,
            authorities: BTreeSet::new(),
        }
    }

    #[must_use]
    pub const fn provenance(&self) -> AbstractProvenance {
        self.provenance
    }

    #[must_use]
    pub const fn range(&self) -> ByteRange {
        self.range
    }

    pub const fn footprint(&self) -> Option<MemoryFootprint> {
        self.footprint
    }
    pub const fn with_footprint(mut self, footprint: Option<MemoryFootprint>) -> Self {
        self.footprint = footprint;
        self
    }
    pub fn actual_range(&self) -> AbstractByteRange {
        self.footprint
            .map_or(AbstractByteRange::Unknown, |f| f.range)
    }

    #[must_use]
    pub const fn kind(&self) -> VirLoanKind {
        self.kind
    }

    #[must_use]
    pub const fn region(&self) -> VirBorrowRegionId {
        self.region
    }

    #[must_use]
    pub const fn parent(&self) -> Option<VirLoanId> {
        self.parent
    }

    #[must_use]
    pub const fn activity(&self) -> LoanActivity {
        self.activity
    }

    pub fn set_activity(&mut self, activity: LoanActivity) {
        self.activity = activity;
    }

    #[must_use]
    pub const fn authorities(&self) -> &BTreeSet<AbstractLoanAuthority> {
        &self.authorities
    }

    #[must_use]
    pub fn with_authority(mut self, authority: VirValueId) -> Self {
        self.authorities
            .insert(AbstractLoanAuthority::value(authority));
        self
    }

    pub fn add_authority(&mut self, authority: VirValueId) {
        self.authorities
            .insert(AbstractLoanAuthority::value(authority));
    }

    pub fn remove_authority(&mut self, authority: VirValueId) -> bool {
        self.authorities
            .remove(&AbstractLoanAuthority::value(authority))
    }

    pub fn move_authority(&mut self, source: VirValueId, result: VirValueId) -> bool {
        if !self
            .authorities
            .remove(&AbstractLoanAuthority::value(source))
        {
            return false;
        }
        self.authorities
            .insert(AbstractLoanAuthority::value(result));
        true
    }

    #[must_use]
    pub fn has_value_authority(&self, authority: VirValueId) -> bool {
        self.authorities
            .contains(&AbstractLoanAuthority::value(authority))
    }

    pub fn move_authority_to_storage(
        &mut self,
        source: VirValueId,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    ) -> bool {
        if !self
            .authorities
            .remove(&AbstractLoanAuthority::value(source))
        {
            return false;
        }
        self.authorities
            .insert(AbstractLoanAuthority::stored(allocation, payload));
        true
    }

    pub fn move_authority_from_storage(
        &mut self,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
        result: VirValueId,
    ) -> bool {
        if !self
            .authorities
            .remove(&AbstractLoanAuthority::stored(allocation, payload))
        {
            return false;
        }
        self.authorities
            .insert(AbstractLoanAuthority::value(result));
        true
    }

    pub fn add_stored_authority(
        &mut self,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    ) {
        self.authorities
            .insert(AbstractLoanAuthority::stored(allocation, payload));
    }

    pub fn remove_stored_authority(
        &mut self,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    ) -> bool {
        self.authorities
            .remove(&AbstractLoanAuthority::stored(allocation, payload))
    }

    pub fn move_stored_authority(
        &mut self,
        source_allocation: AbstractAllocationId,
        source_payload: ResourcePayloadKey,
        destination_allocation: AbstractAllocationId,
        destination_payload: ResourcePayloadKey,
    ) -> bool {
        if !self.authorities.remove(&AbstractLoanAuthority::stored(
            source_allocation,
            source_payload,
        )) {
            return false;
        }
        self.authorities.insert(AbstractLoanAuthority::stored(
            destination_allocation,
            destination_payload,
        ));
        true
    }

    fn join(&self, other: &Self, loan: VirLoanId) -> Result<Self, ResourceJoinError> {
        if self.range != other.range
            || self.kind != other.kind
            || self.region != other.region
            || self.parent != other.parent
        {
            return Err(ResourceJoinError::LoanMetadataMismatch { loan });
        }
        let mut authorities = self.authorities.clone();
        authorities.extend(other.authorities.iter().copied());
        Ok(Self {
            provenance: self.provenance.join(other.provenance),
            footprint: match (self.footprint, other.footprint) {
                (Some(a), Some(b)) => a.join(b),
                _ => None,
            },
            activity: self.activity.join(other.activity),
            authorities,
            ..self.clone()
        })
    }

    fn join_absent(&self) -> Self {
        let mut joined = self.clone();
        if !matches!(joined.activity, LoanActivity::Ended) {
            joined.activity = LoanActivity::MaybeActive;
        }
        joined
    }

    fn project_cfg_edge(&self, remapper: &ExpressionRemapper) -> Self {
        let renames = &remapper.roots;
        let authorities = self
            .authorities
            .iter()
            .map(|authority| match authority {
                AbstractLoanAuthority::Value(value) => {
                    AbstractLoanAuthority::Value(renames.get(value).copied().unwrap_or(*value))
                }
                AbstractLoanAuthority::Stored { .. } => *authority,
            })
            .collect();
        Self {
            authorities,
            footprint: self.footprint.map(|f| f.project(remapper)),
            ..self.clone()
        }
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
    interval: U64Interval,
    pointer: AbstractPointer,
    access: VirMemoryAccess,
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
    fn join(self, other: Self, value: VirValueId) -> Result<Self, ResourceJoinError> {
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

    fn widen(self, next: Self, value: VirValueId) -> Result<Self, ResourceJoinError> {
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

/// A normalized path fact derived from program structure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PathFact {
    Boolean {
        value: VirValueId,
        expected: bool,
    },
    Comparison {
        predicate: VirIntegerPredicate,
        left: VirValueId,
        right: VirValueId,
    },
}

impl PathFact {
    #[must_use]
    pub const fn boolean(value: VirValueId, expected: bool) -> Self {
        Self::Boolean { value, expected }
    }

    /// Creates a canonical comparison. Symmetric predicates and reversed
    /// operands normalize to one representation.
    #[must_use]
    pub const fn comparison(
        predicate: VirIntegerPredicate,
        left: VirValueId,
        right: VirValueId,
    ) -> Self {
        if left.get() <= right.get() {
            Self::Comparison {
                predicate,
                left,
                right,
            }
        } else {
            Self::Comparison {
                predicate: swap_comparison_operands(predicate),
                left: right,
                right: left,
            }
        }
    }

    #[must_use]
    pub const fn negated(self) -> Self {
        match self {
            Self::Boolean { value, expected } => Self::Boolean {
                value,
                expected: !expected,
            },
            Self::Comparison {
                predicate,
                left,
                right,
            } => Self::Comparison {
                predicate: negate_comparison(predicate),
                left,
                right,
            },
        }
    }

    const fn constant_truth(self) -> Option<bool> {
        match self {
            Self::Comparison {
                predicate,
                left,
                right,
            } if left.get() == right.get() => Some(matches!(
                predicate,
                VirIntegerPredicate::Equal
                    | VirIntegerPredicate::LessOrEqual
                    | VirIntegerPredicate::GreaterOrEqual
            )),
            Self::Boolean { .. } | Self::Comparison { .. } => None,
        }
    }
}

const fn swap_comparison_operands(predicate: VirIntegerPredicate) -> VirIntegerPredicate {
    match predicate {
        VirIntegerPredicate::Equal => VirIntegerPredicate::Equal,
        VirIntegerPredicate::NotEqual => VirIntegerPredicate::NotEqual,
        VirIntegerPredicate::LessThan => VirIntegerPredicate::GreaterThan,
        VirIntegerPredicate::LessOrEqual => VirIntegerPredicate::GreaterOrEqual,
        VirIntegerPredicate::GreaterThan => VirIntegerPredicate::LessThan,
        VirIntegerPredicate::GreaterOrEqual => VirIntegerPredicate::LessOrEqual,
    }
}

const fn negate_comparison(predicate: VirIntegerPredicate) -> VirIntegerPredicate {
    match predicate {
        VirIntegerPredicate::Equal => VirIntegerPredicate::NotEqual,
        VirIntegerPredicate::NotEqual => VirIntegerPredicate::Equal,
        VirIntegerPredicate::LessThan => VirIntegerPredicate::GreaterOrEqual,
        VirIntegerPredicate::LessOrEqual => VirIntegerPredicate::GreaterThan,
        VirIntegerPredicate::GreaterThan => VirIntegerPredicate::LessOrEqual,
        VirIntegerPredicate::GreaterOrEqual => VirIntegerPredicate::LessThan,
    }
}

/// Conjunctive facts that hold on every execution represented by a state.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathCondition {
    Unreachable,
    Reachable(BTreeSet<PathFact>),
}

impl PathCondition {
    #[must_use]
    pub const fn empty() -> Self {
        Self::Reachable(BTreeSet::new())
    }

    #[must_use]
    pub const fn unreachable() -> Self {
        Self::Unreachable
    }

    #[must_use]
    pub const fn is_reachable(&self) -> bool {
        matches!(self, Self::Reachable(_))
    }

    #[must_use]
    pub const fn facts(&self) -> Option<&BTreeSet<PathFact>> {
        match self {
            Self::Unreachable => None,
            Self::Reachable(facts) => Some(facts),
        }
    }

    #[must_use]
    pub fn atom_count(&self) -> usize {
        self.facts().map_or(0, BTreeSet::len)
    }

    #[must_use]
    pub fn implies(&self, fact: PathFact) -> bool {
        match self {
            Self::Unreachable => true,
            Self::Reachable(facts) => facts.contains(&fact),
        }
    }

    /// Adds one structurally derived fact. A direct fact/negation conflict
    /// makes the path unreachable; deeper solver reasoning belongs to 5.2+.
    pub fn conjoin(&mut self, fact: PathFact) {
        let Self::Reachable(facts) = self else {
            return;
        };
        if let Some(truth) = fact.constant_truth() {
            if !truth {
                *self = Self::Unreachable;
            }
            return;
        }
        if facts.contains(&fact.negated()) {
            *self = Self::Unreachable;
        } else {
            facts.insert(fact);
        }
    }

    /// Facts guaranteed on either incoming path. Unreachable is the join
    /// identity because it contributes no concrete executions.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Unreachable, right) => right.clone(),
            (left, Self::Unreachable) => left.clone(),
            (Self::Reachable(left), Self::Reachable(right)) => {
                Self::Reachable(left.intersection(right).copied().collect())
            }
        }
    }

    fn project(&self, renames: &[(VirValueId, VirValueId)]) -> Self {
        let Self::Reachable(facts) = self else {
            return Self::Unreachable;
        };
        // Repeated scalar arguments are legal. Keeping one deterministic
        // target per source retains a sound subset without a Cartesian blowup.
        let mut first_target_by_source = BTreeMap::new();
        for &(source, target) in renames {
            first_target_by_source.entry(source).or_insert(target);
        }

        let mut projected = Self::empty();
        for fact in facts {
            let renamed = match *fact {
                PathFact::Boolean { value, expected } => first_target_by_source
                    .get(&value)
                    .copied()
                    .map(|value| PathFact::boolean(value, expected)),
                PathFact::Comparison {
                    predicate,
                    left,
                    right,
                } => first_target_by_source
                    .get(&left)
                    .copied()
                    .zip(first_target_by_source.get(&right).copied())
                    .map(|(left, right)| PathFact::comparison(predicate, left, right)),
            };
            if let Some(fact) = renamed {
                projected.conjoin(fact);
            }
        }
        projected
    }
}

impl Default for PathCondition {
    fn default() -> Self {
        Self::empty()
    }
}

/// Complete abstract resource facts at one VIR program point.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ResourceState {
    relations: RelationState,
    path_condition: PathCondition,
    allocations: BTreeMap<AbstractAllocationId, AbstractAllocation>,
    values: BTreeMap<VirValueId, AbstractValue>,
    word_expressions: BTreeMap<VirValueId, AffineExpression>,
    loans: BTreeMap<VirLoanId, AbstractLoan>,
    loan_precision_losses: BTreeSet<LoanPrecisionLoss>,
}

impl ResourceState {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            relations: RelationState::new(),
            path_condition: PathCondition::empty(),
            allocations: BTreeMap::new(),
            values: BTreeMap::new(),
            word_expressions: BTreeMap::new(),
            loans: BTreeMap::new(),
            loan_precision_losses: BTreeSet::new(),
        }
    }

    #[must_use]
    pub const fn unreachable() -> Self {
        Self {
            relations: RelationState::new(),
            path_condition: PathCondition::unreachable(),
            allocations: BTreeMap::new(),
            values: BTreeMap::new(),
            word_expressions: BTreeMap::new(),
            loans: BTreeMap::new(),
            loan_precision_losses: BTreeSet::new(),
        }
    }

    #[must_use]
    pub const fn path_condition(&self) -> &PathCondition {
        &self.path_condition
    }

    pub fn conjoin_path_fact(&mut self, fact: PathFact) {
        self.path_condition.conjoin(fact);
    }

    pub(super) fn forget_path_condition(&mut self) {
        if self.path_condition.is_reachable() {
            self.path_condition = PathCondition::empty();
        }
    }

    pub(super) fn same_resource_facts(&self, other: &Self) -> bool {
        self.allocations == other.allocations
            && resource_values(&self.values) == resource_values(&other.values)
            && self.loans == other.loans
            && self.loan_precision_losses == other.loan_precision_losses
    }

    #[must_use]
    pub const fn allocations(&self) -> &BTreeMap<AbstractAllocationId, AbstractAllocation> {
        &self.allocations
    }

    #[must_use]
    pub fn allocation(&self, id: AbstractAllocationId) -> Option<&AbstractAllocation> {
        self.allocations.get(&id)
    }

    pub fn allocation_mut(&mut self, id: AbstractAllocationId) -> Option<&mut AbstractAllocation> {
        self.allocations.get_mut(&id)
    }

    pub fn define_allocation(
        &mut self,
        id: AbstractAllocationId,
        allocation: AbstractAllocation,
    ) -> Result<(), ResourceStateDefinitionError> {
        if !self.allocations.contains_key(&id)
            && self.allocations.len() >= instance::MAX_ALLOCATION_SLOTS
        {
            return Err(ResourceStateDefinitionError::AllocationInstanceBudget);
        }
        match self.allocations.entry(id) {
            Entry::Vacant(entry) => {
                entry.insert(allocation);
                Ok(())
            }
            Entry::Occupied(_) => Err(ResourceStateDefinitionError::DuplicateAllocation(id)),
        }
    }

    pub(super) fn replace_allocation(
        &mut self,
        id: AbstractAllocationId,
        allocation: AbstractAllocation,
    ) {
        self.allocations.insert(id, allocation);
    }

    #[must_use]
    pub const fn values(&self) -> &BTreeMap<VirValueId, AbstractValue> {
        &self.values
    }

    #[must_use]
    pub fn value(&self, id: VirValueId) -> Option<&AbstractValue> {
        self.values.get(&id)
    }

    pub fn value_mut(&mut self, id: VirValueId) -> Option<&mut AbstractValue> {
        // Arbitrary abstract-value replacement cannot retain old numeric
        // relations. Branch narrowing uses the monotone helper below instead.
        self.relations.forget_value(id);
        self.values.get_mut(&id)
    }

    pub fn relations(&self) -> &RelationState {
        &self.relations
    }

    pub(in crate::verifier) fn learn_relations(
        &mut self,
        premises: &[DifferencePremise],
        limits: DifferenceLimits,
    ) {
        self.relations.learn(premises, &self.values, limits);
        self.reduce_relation_intervals();
    }

    pub(in crate::verifier) fn limit_relations(&mut self, limits: DifferenceLimits) {
        self.relations.limit(limits);
    }

    pub(in crate::verifier) fn reduce_relation_intervals(&mut self) {
        // These bounds are already established in this whole resource case;
        // narrowing never imports a goal or a guessed loop invariant.
        for bound in self.relations.bounds().collect::<Vec<_>>() {
            let refinement = match (bound.left, bound.right) {
                (Some(value), None) => u64::try_from(bound.bound)
                    .ok()
                    .map(|upper| (value, 0, upper)),
                (None, Some(value)) => bound
                    .bound
                    .checked_neg()
                    .and_then(|n| u64::try_from(n).ok())
                    .map(|lower| (value, lower, u64::MAX)),
                _ => None,
            };
            if let Some((value, lower, upper)) = refinement {
                self.narrow_word_interval(
                    value,
                    U64Interval::new(lower, upper).expect("ordered unsigned relation bound"),
                );
            }
        }
    }

    pub(in crate::verifier) fn narrow_word_interval(
        &mut self,
        id: VirValueId,
        interval: U64Interval,
    ) {
        if let Some(AbstractValue::U64(current)) = self.values.get_mut(&id)
            && let Some(narrowed) = current.intersection(interval)
        {
            *current = narrowed;
        }
    }

    pub fn define_value(
        &mut self,
        id: VirValueId,
        value: AbstractValue,
    ) -> Result<(), ResourceStateDefinitionError> {
        match self.values.entry(id) {
            Entry::Vacant(entry) => {
                entry.insert(value);
                Ok(())
            }
            Entry::Occupied(_) => Err(ResourceStateDefinitionError::DuplicateValue(id)),
        }
    }

    #[must_use]
    pub fn word_expression(&self, id: VirValueId) -> Option<AffineExpression> {
        self.word_expressions.get(&id).copied()
    }

    pub(super) fn set_word_expression(&mut self, id: VirValueId, expression: AffineExpression) {
        self.word_expressions.insert(id, expression);
    }

    pub(super) fn clear_word_expression(&mut self, id: VirValueId) {
        self.word_expressions.remove(&id);
    }

    #[must_use]
    pub const fn loans(&self) -> &BTreeMap<VirLoanId, AbstractLoan> {
        &self.loans
    }

    #[must_use]
    pub fn loan(&self, id: VirLoanId) -> Option<&AbstractLoan> {
        self.loans.get(&id)
    }

    pub fn loan_mut(&mut self, id: VirLoanId) -> Option<&mut AbstractLoan> {
        self.loans.get_mut(&id)
    }

    pub fn define_loan(
        &mut self,
        id: VirLoanId,
        loan: AbstractLoan,
    ) -> Result<(), ResourceStateDefinitionError> {
        match self.loans.entry(id) {
            Entry::Vacant(entry) => {
                entry.insert(loan);
                Ok(())
            }
            Entry::Occupied(_) => Err(ResourceStateDefinitionError::DuplicateLoan(id)),
        }
    }

    /// Installs the next dynamic instance of one statically unique loan site.
    /// A loop may execute that site again only after the previous instance is
    /// definitely ended; live or uncertain instances remain a closed error.
    pub(super) fn define_next_loan_instance(
        &mut self,
        id: VirLoanId,
        loan: AbstractLoan,
    ) -> Result<(), ResourceStateDefinitionError> {
        match self.loans.entry(id) {
            Entry::Vacant(entry) => {
                entry.insert(loan);
                Ok(())
            }
            Entry::Occupied(mut entry) if matches!(entry.get().activity(), LoanActivity::Ended) => {
                entry.insert(loan);
                Ok(())
            }
            Entry::Occupied(_) => Err(ResourceStateDefinitionError::DuplicateLoan(id)),
        }
    }

    pub fn mark_loan_precision_loss(&mut self, loss: LoanPrecisionLoss) {
        self.loan_precision_losses.insert(loss);
    }

    #[must_use]
    pub const fn loan_precision_losses(&self) -> &BTreeSet<LoanPrecisionLoss> {
        &self.loan_precision_losses
    }

    pub(super) fn project_value_for_cfg(
        &self,
        source: VirValueId,
        renames: &[(VirValueId, VirValueId)],
    ) -> Option<AbstractValue> {
        let remapper = ExpressionRemapper::new(self, renames);
        self.value(source)
            .copied()
            .map(|value| remapper.value(value))
    }

    /// Keeps allocation facts while projecting path facts onto CFG edge
    /// arguments. Target values are deliberately left empty for the CFG
    /// transfer to define after checking types and linear permission moves.
    #[must_use]
    pub(super) fn project_cfg_edge(&self, renames: &[(VirValueId, VirValueId)]) -> Self {
        if !self.path_condition.is_reachable() {
            return Self::unreachable();
        }
        let remapper = ExpressionRemapper::new(self, renames);
        let mut word_expressions = BTreeMap::new();
        for &(source, target) in renames {
            if let Some(expression) = self.word_expression(source)
                && let Some(expression) = remapper.expression(expression)
            {
                word_expressions.entry(target).or_insert(expression);
            }
        }
        Self {
            path_condition: self.path_condition.project(renames),
            relations: self.relations.project(
                &renames
                    .iter()
                    .copied()
                    .filter(|(source, _)| {
                        matches!(self.value(*source), Some(AbstractValue::U64(_)))
                    })
                    .collect::<Vec<_>>(),
            ),
            allocations: self
                .allocations
                .iter()
                .map(|(id, allocation)| (*id, allocation.project_cfg_edge(&remapper, &self.values)))
                .collect(),
            values: BTreeMap::new(),
            word_expressions,
            loans: self
                .loans
                .iter()
                .map(|(id, loan)| (*id, loan.project_cfg_edge(&remapper)))
                .collect(),
            loan_precision_losses: self.loan_precision_losses.clone(),
        }
    }

    /// Least upper bound for control-flow convergence.
    ///
    /// Value facts missing from either reachable predecessor are dropped, but
    /// outstanding allocation ownership is retained conservatively. CFG edge
    /// transfer must rename arguments to target block parameters before this
    /// operation, so retaining only common value IDs is intentional.
    pub fn join(&self, other: &Self) -> Result<Self, ResourceJoinError> {
        if !self.path_condition.is_reachable() {
            return Ok(other.clone());
        }
        if !other.path_condition.is_reachable() {
            return Ok(self.clone());
        }

        let allocations = instance::join_allocations(&self.allocations, &other.allocations)?;

        let mut values = BTreeMap::new();
        for (id, left) in &self.values {
            if let Some(right) = other.values.get(id) {
                values.insert(*id, (*left).join(*right, *id)?);
            }
        }

        let mut word_expressions = BTreeMap::new();
        for (id, left) in &self.word_expressions {
            if other.word_expressions.get(id) == Some(left) {
                word_expressions.insert(*id, *left);
            }
        }

        let (loans, loan_join_lost) = join_loans(&self.loans, &other.loans)?;
        let mut loan_precision_losses = self.loan_precision_losses.clone();
        loan_precision_losses.extend(other.loan_precision_losses.iter().copied());
        if loan_join_lost {
            loan_precision_losses.insert(LoanPrecisionLoss::LoanJoin);
        }

        Ok(Self {
            path_condition: self.path_condition.join(&other.path_condition),
            relations: self.relations.join(&other.relations),
            allocations,
            values,
            word_expressions,
            loans,
            loan_precision_losses,
        })
    }

    /// Widening for cyclic CFG entries.
    ///
    /// Structural/resource components use their conservative join while
    /// numeric and pointer-offset intervals accelerate expanding bounds to the
    /// domain limits. Callers must first establish that `next` is an ascending
    /// join successor of `self`.
    pub fn widen(&self, next: &Self) -> Result<Self, ResourceJoinError> {
        if !self.path_condition.is_reachable() {
            return Ok(next.clone());
        }
        if !next.path_condition.is_reachable() {
            return Ok(self.clone());
        }

        let allocations = instance::join_allocations(&self.allocations, &next.allocations)?;

        let mut values = BTreeMap::new();
        for (id, current) in &self.values {
            if let Some(next) = next.values.get(id) {
                values.insert(*id, (*current).widen(*next, *id)?);
            }
        }

        let mut word_expressions = BTreeMap::new();
        for (id, current) in &self.word_expressions {
            if next.word_expressions.get(id) == Some(current) {
                word_expressions.insert(*id, *current);
            }
        }

        let (loans, loan_widening_lost) = join_loans(&self.loans, &next.loans)?;
        let mut loan_precision_losses = self.loan_precision_losses.clone();
        loan_precision_losses.extend(next.loan_precision_losses.iter().copied());
        if loan_widening_lost {
            loan_precision_losses.insert(LoanPrecisionLoss::LoanLoopWidening);
        }

        Ok(Self {
            path_condition: self.path_condition.join(&next.path_condition),
            relations: self.relations.widen(&next.relations),
            allocations,
            values,
            word_expressions,
            loans,
            loan_precision_losses,
        })
    }
}

fn join_loans(
    left: &BTreeMap<VirLoanId, AbstractLoan>,
    right: &BTreeMap<VirLoanId, AbstractLoan>,
) -> Result<(BTreeMap<VirLoanId, AbstractLoan>, bool), ResourceJoinError> {
    let mut joined = BTreeMap::new();
    let mut precision_lost = false;
    for id in left
        .keys()
        .chain(right.keys())
        .copied()
        .collect::<BTreeSet<_>>()
    {
        let loan = match (left.get(&id), right.get(&id)) {
            (Some(left), Some(right)) => {
                let result = left.join(right, id)?;
                // Ended, authority-free instances are tombstones only. Their
                // old offsets can differ across loop iterations without
                // losing any live alias/permission obligation.
                let ended = left.activity == LoanActivity::Ended
                    && right.activity == LoanActivity::Ended
                    && left.authorities.is_empty()
                    && right.authorities.is_empty();
                precision_lost |= !ended && (result != *left || result != *right);
                Some(result)
            }
            // An ended loan carries no live authority.  Dropping its
            // tombstone when the other alternative has never executed that
            // static site is exact, and lets a loop-local LoanBegin represent
            // a fresh dynamic instance on the next iteration.
            (Some(loan), None) | (None, Some(loan))
                if matches!(loan.activity(), LoanActivity::Ended) =>
            {
                None
            }
            (Some(loan), None) | (None, Some(loan)) => {
                let result = loan.join_absent();
                precision_lost |=
                    result != *loan || !matches!(loan.activity(), LoanActivity::Ended);
                Some(result)
            }
            (None, None) => unreachable!(),
        };
        if let Some(loan) = loan {
            joined.insert(id, loan);
        }
    }
    Ok((joined, precision_lost))
}

fn resource_values(
    values: &BTreeMap<VirValueId, AbstractValue>,
) -> BTreeMap<VirValueId, AbstractValue> {
    values
        .iter()
        .filter_map(|(id, value)| {
            matches!(
                value,
                AbstractValue::Pointer(_)
                    | AbstractValue::Permission(_)
                    | AbstractValue::EnumDiscriminant(_)
            )
            .then_some((*id, *value))
        })
        .collect()
}

struct ExpressionRemapper {
    roots: BTreeMap<VirValueId, VirValueId>,
    expressions: Vec<(AffineExpression, VirValueId)>,
    prefix_expressions: Vec<(AffineExpression, VirValueId)>,
}

impl ExpressionRemapper {
    fn new(state: &ResourceState, renames: &[(VirValueId, VirValueId)]) -> Self {
        let mut roots = BTreeMap::new();
        let mut expressions = Vec::new();
        let mut prefix_expressions = Vec::new();
        for &(source, target) in renames {
            roots.entry(source).or_insert(target);
            if let Some(AbstractValue::U64(value)) = state.value(source) {
                prefix_expressions.push((AffineExpression::identity(source), target));
                let expression = state.word_expression(source).unwrap_or_else(|| {
                    value
                        .exact_value()
                        .map(AffineExpression::constant)
                        .unwrap_or_else(|| AffineExpression::identity(source))
                });
                prefix_expressions.push((expression, target));
            }
            if let Some(expression) = state.word_expression(source)
                && !expressions.iter().any(|(known, _)| *known == expression)
            {
                expressions.push((expression, target));
            }
        }
        // An identity-view result (or zero-start slice length) can carry a
        // root under a new SSA ID. Only exact x aliases may rename scaled
        // endpoints; arbitrary x+k expressions are not treated as identities.
        for (expression, target) in &expressions {
            if expression.scale() == 1
                && expression.addend() == 0
                && let Some(root) = expression.root()
            {
                roots.entry(root).or_insert(*target);
            }
        }
        Self {
            roots,
            expressions,
            prefix_expressions,
        }
    }

    fn expression(&self, expression: AffineExpression) -> Option<AffineExpression> {
        if expression.is_constant() {
            return Some(expression);
        }
        // Preserve a fixed-stride decomposition when every root is carried
        // by the edge. Replacing i+width with a fresh endpoint identity loses
        // the chunk width and forces unnecessary DBM equalities/closure.
        if let Some(renamed) = expression.rename_root(&self.roots) {
            return Some(renamed);
        }
        if let Some((_, target)) = self
            .expressions
            .iter()
            .find(|(known, _)| *known == expression)
        {
            return Some(AffineExpression::identity(*target));
        }
        None
    }

    fn bound(&self, bound: SymbolicRangeBound) -> Option<SymbolicRangeBound> {
        Some(SymbolicRangeBound::new(
            self.expression(bound.expression())?,
            bound.interval(),
        ))
    }

    fn range(&self, range: AbstractByteRange) -> AbstractByteRange {
        match range {
            AbstractByteRange::Exact(_) | AbstractByteRange::Unknown => range,
            AbstractByteRange::Symbolic { start, end } => {
                match (self.bound(start), self.bound(end)) {
                    (Some(start), Some(end)) => AbstractByteRange::from_bounds(start, end),
                    _ => AbstractByteRange::Unknown,
                }
            }
        }
    }

    fn value(&self, value: AbstractValue) -> AbstractValue {
        match value {
            AbstractValue::Pointer(pointer) => AbstractValue::Pointer(self.pointer(pointer)),
            AbstractValue::Permission(permission) => {
                AbstractValue::Permission(self.permission(permission))
            }
            AbstractValue::EnumDiscriminant(fact) => {
                AbstractValue::EnumDiscriminant(EnumDiscriminantFact::new(
                    fact.interval(),
                    self.pointer(fact.pointer()),
                    fact.access(),
                ))
            }
            AbstractValue::U64(_) | AbstractValue::Bool(_) => value,
        }
    }

    fn pointer(&self, pointer: AbstractPointer) -> AbstractPointer {
        pointer
            .with_domain(match pointer.domain() {
                crate::VirPointerDomain::Restricted(range) => {
                    crate::VirPointerDomain::Restricted(self.range(range))
                }
                domain => domain,
            })
            .with_slice_footprint(pointer.slice_footprint.map(|f| f.project(self)))
            .with_offset_expression(
                pointer
                    .offset_expression()
                    .and_then(|expression| self.expression(expression)),
            )
    }

    fn permission(&self, permission: AbstractPermission) -> AbstractPermission {
        AbstractPermission::new(
            permission.provenance(),
            self.range(permission.range()),
            permission.access(),
            permission.free_capability(),
        )
        .with_availability(permission.availability())
        .with_authority(permission.authority())
    }
}

/// One atomic path-local resource state. Stage 7.1.4 may place bounded guards
/// around cases, but the facts inside a case continue to have this sole owner.
pub type ResourceCase = ResourceState;

/// Invalid definitions or unavailable fresh-instance capacity in one state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceStateDefinitionError {
    AllocationInstanceBudget,
    AllocationInstanceStillReferenced(AbstractAllocationId),
    DuplicateAllocation(AbstractAllocationId),
    DuplicateValue(VirValueId),
    DuplicateLoan(VirLoanId),
}

impl fmt::Display for ResourceStateDefinitionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AllocationInstanceBudget => {
                formatter.write_str("allocation instance slot budget exhausted")
            }
            Self::AllocationInstanceStillReferenced(allocation) => write!(
                formatter,
                "cannot reuse allocation slot {allocation}: a previous instance may still own resources or loan authority"
            ),
            Self::DuplicateAllocation(allocation) => write!(
                formatter,
                "abstract allocation {allocation} is defined more than once"
            ),
            Self::DuplicateValue(value) => {
                write!(
                    formatter,
                    "abstract value %{} is defined more than once",
                    value.get()
                )
            }
            Self::DuplicateLoan(loan) => {
                write!(
                    formatter,
                    "abstract loan l{} is defined more than once",
                    loan.get()
                )
            }
        }
    }
}

impl Error for ResourceStateDefinitionError {}

/// Metadata mismatch or exhausted allocation capacity at a resource-state join.
///
/// These fail analysis rather than returning a partial resource state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceJoinError {
    AllocationInstanceBudget,
    AllocationRegionMismatch { allocation: AbstractAllocationId },
    AllocationSizeMismatch { allocation: AbstractAllocationId },
    AllocationAlignmentMismatch { allocation: AbstractAllocationId },
    ValueKindMismatch { value: VirValueId },
    LoanMetadataMismatch { loan: VirLoanId },
}

impl fmt::Display for ResourceJoinError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AllocationInstanceBudget => formatter
                .write_str("allocation instance slot budget exhausted at resource-state join"),
            Self::AllocationRegionMismatch { allocation } => write!(
                formatter,
                "allocation {allocation} has inconsistent regions at resource-state join"
            ),
            Self::AllocationSizeMismatch { allocation } => write!(
                formatter,
                "allocation {allocation} has inconsistent sizes at resource-state join"
            ),
            Self::AllocationAlignmentMismatch { allocation } => write!(
                formatter,
                "allocation {allocation} has inconsistent alignments at resource-state join"
            ),
            Self::ValueKindMismatch { value } => write!(
                formatter,
                "value %{} has inconsistent kinds at resource-state join",
                value.get()
            ),
            Self::LoanMetadataMismatch { loan } => write!(
                formatter,
                "loan l{} has inconsistent immutable metadata at resource-state join",
                loan.get()
            ),
        }
    }
}

impl Error for ResourceJoinError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn range(start: u64, end: u64) -> ByteRange {
        ByteRange::new(start, end).expect("test range must be valid")
    }

    fn allocation(size: u64) -> AbstractAllocation {
        AbstractAllocation::new(VirRegionId::new(0), size, 8)
            .expect("test allocation must be valid")
    }

    #[test]
    fn byte_set_normalizes_insert_remove_and_intersection() {
        let mut bytes = ByteSet::new();
        bytes.insert(range(8, 16));
        bytes.insert(range(0, 8));
        bytes.insert(range(24, 32));
        assert_eq!(bytes.ranges(), &[range(0, 16), range(24, 32)]);

        bytes.remove(range(4, 28));
        assert_eq!(bytes.ranges(), &[range(0, 4), range(28, 32)]);
        assert!(bytes.contains(range(1, 3)));
        assert!(!bytes.contains(range(3, 29)));

        let other = ByteSet::single(range(2, 30));
        assert_eq!(bytes.union(&other).ranges(), &[range(0, 32)]);
        assert_eq!(
            bytes.intersection(&other).ranges(),
            &[range(2, 4), range(28, 30)]
        );
    }

    #[test]
    fn byte_set_matches_a_small_concrete_bitmap_model() {
        fn from_mask(mask: u8) -> ByteSet {
            let mut result = ByteSet::new();
            for byte in 0..8 {
                if mask & (1 << byte) != 0 {
                    result.insert(range(byte, byte + 1));
                }
            }
            result
        }

        for left_mask in u8::MIN..=u8::MAX {
            let left = from_mask(left_mask);
            for right_mask in u8::MIN..=u8::MAX {
                let right = from_mask(right_mask);
                let intersection = left.intersection(&right);
                assert_eq!(intersection, from_mask(left_mask & right_mask));
                assert_eq!(left.is_disjoint(&right), left_mask & right_mask == 0);
            }
        }
    }

    #[test]
    fn byte_and_object_state_budgets_only_lose_precision() {
        let mut bytes = ByteSet::new();
        for index in 0..=VERIFIER_BYTE_SET_MAX_RANGES {
            let start = u64::try_from(index).unwrap() * 2;
            bytes.insert(range(start, start + 1));
        }
        assert_eq!(bytes.ranges().len(), VERIFIER_BYTE_SET_MAX_RANGES);
        assert!(!bytes.is_precise());
        assert!(!bytes.contains(range(
            u64::try_from(VERIFIER_BYTE_SET_MAX_RANGES).unwrap() * 2,
            u64::try_from(VERIFIER_BYTE_SET_MAX_RANGES).unwrap() * 2 + 1,
        )));

        let access = VirMemoryAccess::core_u64();
        let mut objects = ObjectState::new();
        for offset in 0..VERIFIER_OBJECT_STATE_MAX_ENTRIES {
            assert!(objects.set_active_variant(
                ObjectStateKey::new(u64::try_from(offset).unwrap(), access),
                ActiveVariantState::Exact(VirVariantId::new(0)),
            ));
        }
        assert!(!objects.set_active_variant(
            ObjectStateKey::new(
                u64::try_from(VERIFIER_OBJECT_STATE_MAX_ENTRIES).unwrap(),
                access,
            ),
            ActiveVariantState::Exact(VirVariantId::new(0)),
        ));
        assert!(!objects.is_precise());
        assert_eq!(
            objects.active_variant(ObjectStateKey::new(
                VERIFIER_OBJECT_STATE_MAX_ENTRIES as u64,
                access,
            )),
            ActiveVariantState::Unknown
        );

        let allocation_id = AbstractAllocationId::new(7);
        let payload = TypedResourcePayload::new(
            AbstractPointer::new(
                AbstractProvenance::Known(allocation_id),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            ),
            AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(range(0, 8)),
                AccessPermission::Write,
                FreeCapability::Yes,
            ),
        );
        let mut payloads = ObjectState::new();
        for offset in 0..VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES {
            assert!(payloads.set_resource_payload(
                ResourcePayloadKey::new(u64::try_from(offset).unwrap(), access),
                MovePathState::available(payload),
            ));
        }
        assert!(!payloads.set_resource_payload(
            ResourcePayloadKey::new(
                u64::try_from(VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES).unwrap(),
                access,
            ),
            MovePathState::available(payload),
        ));
        assert!(!payloads.is_precise());
        assert_eq!(
            payloads.resource_payload(ResourcePayloadKey::new(
                VERIFIER_RESOURCE_PAYLOAD_MAX_ENTRIES as u64,
                access,
            )),
            MovePathState::Unknown
        );

        let left = ActiveVariantState::Alternatives(
            (0..VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES)
                .map(|variant| VirVariantId::new(u32::try_from(variant).unwrap()))
                .collect(),
        );
        assert_eq!(
            left.join(&ActiveVariantState::Exact(VirVariantId::new(
                u32::try_from(VERIFIER_ACTIVE_VARIANT_MAX_ALTERNATIVES).unwrap(),
            ))),
            ActiveVariantState::Unknown
        );
    }

    #[test]
    fn only_authority_free_ended_tombstones_can_ignore_historical_footprint_changes() {
        let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
        for activity in [
            LoanActivity::Ended,
            LoanActivity::Active,
            LoanActivity::MaybeActive,
        ] {
            for has_authority in [false, true] {
                let make = |start| {
                    let mut loan = AbstractLoan::new(
                        provenance,
                        range(0, 32),
                        VirLoanKind::Mutable,
                        VirBorrowRegionId::new(0),
                        None,
                        activity,
                    )
                    .with_footprint(Some(MemoryFootprint {
                        provenance,
                        access: VirMemoryAccess::core_u64(),
                        stride_bytes: 8,
                        range: AbstractByteRange::Exact(range(start, start + 8)),
                        envelope: range(start, start + 8),
                    }));
                    if has_authority {
                        loan = loan.with_authority(VirValueId::new(0));
                    }
                    BTreeMap::from([(VirLoanId::new(0), loan)])
                };
                let (joined, lost) = join_loans(&make(0), &make(8)).unwrap();
                assert_eq!(lost, activity != LoanActivity::Ended || has_authority);
                assert_eq!(joined[&VirLoanId::new(0)].activity(), activity);
                assert_eq!(
                    joined[&VirLoanId::new(0)].authorities().is_empty(),
                    !has_authority
                );
            }
        }
    }

    #[test]
    fn initialization_join_keeps_only_definite_common_bytes() {
        let mut left = allocation(32);
        let mut right = allocation(32);
        left.mark_initialized(range(0, 16)).unwrap();
        right.mark_initialized(range(8, 24)).unwrap();

        let joined = left.join(AbstractAllocationId::new(0), &right).unwrap();
        assert_eq!(
            joined.initialization().classify(range(8, 16)),
            InitializationClass::Initialized
        );
        assert_eq!(
            joined.initialization().classify(range(24, 32)),
            InitializationClass::Uninitialized
        );
        assert_eq!(
            joined.initialization().classify(range(0, 8)),
            InitializationClass::MaybeInitialized
        );
        assert_eq!(
            joined.initialization().classify(range(16, 24)),
            InitializationClass::MaybeInitialized
        );
    }

    #[test]
    fn allocation_updates_preserve_disjoint_initialization_facts() {
        let mut value = allocation(24);
        value.mark_initialized(range(8, 16)).unwrap();
        assert!(
            value
                .initialization()
                .initialized()
                .is_disjoint(value.initialization().uninitialized())
        );
        value.forget_initialization(range(12, 20)).unwrap();
        assert_eq!(
            value.initialization().classify(range(12, 20)),
            InitializationClass::MaybeInitialized
        );
        value.mark_uninitialized(range(8, 16)).unwrap();
        assert_eq!(
            value.initialization().classify(range(8, 16)),
            InitializationClass::Uninitialized
        );
        assert_eq!(
            value.mark_initialized(range(16, 25)),
            Err(AbstractAllocationError::RangeOutOfBounds {
                range: range(16, 25),
                size_bytes: 24,
            })
        );
    }

    #[test]
    fn liveness_ownership_and_permission_joins_lose_path_specific_certainty() {
        assert_eq!(
            LivenessState::Live.join(LivenessState::Dead),
            LivenessState::MaybeLive
        );
        assert_eq!(
            OwnershipState::Owned.join(OwnershipState::Unowned),
            OwnershipState::MaybeOwned
        );

        let allocation = AbstractAllocationId::new(4);
        let mut left = AbstractPermission::new(
            AbstractProvenance::Known(allocation),
            AbstractByteRange::Exact(range(0, 16)),
            AccessPermission::Write,
            FreeCapability::Yes,
        );
        let right = AbstractPermission::new(
            AbstractProvenance::Known(allocation),
            AbstractByteRange::Exact(range(8, 16)),
            AccessPermission::Read,
            FreeCapability::No,
        );
        left.mark_consumed();
        let joined = left.join(right);
        assert_eq!(joined.range(), AbstractByteRange::Unknown);
        assert_eq!(joined.access(), AccessPermission::MaybeWrite);
        assert_eq!(joined.free_capability(), FreeCapability::Maybe);
        assert_eq!(joined.availability(), PermissionAvailability::MaybeConsumed);
    }

    #[test]
    fn pointer_join_tracks_interval_provenance_and_alignment() {
        let u64_access = VirMemoryAccess::core_u64();
        let left = AbstractPointer::new(
            AbstractProvenance::Known(AbstractAllocationId::new(0)),
            U64Interval::exact(8),
            GuaranteedAlignment::new(8).unwrap(),
        )
        .with_memory_access(Some(u64_access));
        let right = AbstractPointer::new(
            AbstractProvenance::Known(AbstractAllocationId::new(1)),
            U64Interval::exact(24),
            GuaranteedAlignment::new(4).unwrap(),
        )
        .with_memory_access(Some(u64_access));
        let joined = left.join(right);
        assert_eq!(joined.provenance(), AbstractProvenance::Unknown);
        assert_eq!(joined.offset_bytes(), U64Interval::new(8, 24).unwrap());
        assert_eq!(joined.alignment().bytes(), 4);
        assert_eq!(joined.memory_access(), Some(u64_access));

        let incompatible = right.with_memory_access(Some(VirMemoryAccess::new(
            crate::VirTypeId::new(1),
            crate::VirLayoutId::new(1),
        )));
        assert_eq!(left.join(incompatible).memory_access(), None);
        assert_eq!(left.widen(incompatible).memory_access(), None);
    }

    #[test]
    fn interval_widening_accelerates_only_outward_moving_bounds() {
        let current = U64Interval::new(4, 8).unwrap();
        assert_eq!(current.widen(current), current);
        assert_eq!(
            current.widen(U64Interval::new(2, 8).unwrap()),
            U64Interval::new(0, 8).unwrap()
        );
        assert_eq!(
            current.widen(U64Interval::new(4, 16).unwrap()),
            U64Interval::new(4, u64::MAX).unwrap()
        );
        assert_eq!(
            current.widen(U64Interval::new(2, 16).unwrap()),
            U64Interval::unknown()
        );
    }

    #[test]
    fn path_conditions_detect_direct_contradiction_and_intersect_at_join() {
        let shared = PathFact::boolean(VirValueId::new(0), true);
        let left_only = PathFact::comparison(
            VirIntegerPredicate::LessThan,
            VirValueId::new(1),
            VirValueId::new(2),
        );
        let mut left = PathCondition::empty();
        left.conjoin(shared);
        left.conjoin(left_only);
        let mut right = PathCondition::empty();
        right.conjoin(shared);
        right.conjoin(left_only.negated());

        let joined = left.join(&right);
        assert!(joined.implies(shared));
        assert!(!joined.implies(left_only));

        right.conjoin(shared.negated());
        assert_eq!(right, PathCondition::Unreachable);
        assert_eq!(left.join(&right), left);
    }

    #[test]
    fn path_conditions_simplify_reflexive_comparisons() {
        let value = VirValueId::new(3);
        let mut true_fact = PathCondition::empty();
        true_fact.conjoin(PathFact::comparison(
            VirIntegerPredicate::LessOrEqual,
            value,
            value,
        ));
        assert_eq!(true_fact, PathCondition::empty());

        let mut false_fact = PathCondition::empty();
        false_fact.conjoin(PathFact::comparison(
            VirIntegerPredicate::LessThan,
            value,
            value,
        ));
        assert_eq!(false_fact, PathCondition::unreachable());
    }

    #[test]
    fn comparison_normalization_is_operand_order_independent() {
        assert_eq!(
            PathFact::comparison(
                VirIntegerPredicate::LessThan,
                VirValueId::new(9),
                VirValueId::new(2),
            ),
            PathFact::comparison(
                VirIntegerPredicate::GreaterThan,
                VirValueId::new(2),
                VirValueId::new(9),
            )
        );
    }

    #[test]
    fn primitive_joins_are_commutative_idempotent_and_associative() {
        fn assert_laws<T: Copy + fmt::Debug + PartialEq>(values: &[T], join: impl Fn(T, T) -> T) {
            for &left in values {
                assert_eq!(join(left, left), left);
                for &right in values {
                    assert_eq!(join(left, right), join(right, left));
                    for &third in values {
                        assert_eq!(
                            join(join(left, right), third),
                            join(left, join(right, third))
                        );
                    }
                }
            }
        }

        assert_laws(
            &[
                LivenessState::Live,
                LivenessState::Dead,
                LivenessState::MaybeLive,
            ],
            LivenessState::join,
        );
        assert_laws(
            &[
                OwnershipState::Owned,
                OwnershipState::Unowned,
                OwnershipState::MaybeOwned,
            ],
            OwnershipState::join,
        );
        assert_laws(
            &[
                FreeCapability::Yes,
                FreeCapability::No,
                FreeCapability::Maybe,
            ],
            FreeCapability::join,
        );
        assert_laws(
            &[
                PermissionAvailability::Available,
                PermissionAvailability::Consumed,
                PermissionAvailability::MaybeConsumed,
            ],
            PermissionAvailability::join,
        );
        assert_laws(
            &[
                AbstractBool::True,
                AbstractBool::False,
                AbstractBool::Unknown,
            ],
            AbstractBool::join,
        );
        assert_laws(
            &[
                AccessPermission::Read,
                AccessPermission::Write,
                AccessPermission::MaybeWrite,
            ],
            AccessPermission::join,
        );
        assert_laws(
            &[
                AbstractProvenance::Known(AbstractAllocationId::new(0)),
                AbstractProvenance::Known(AbstractAllocationId::new(1)),
                AbstractProvenance::Unknown,
            ],
            AbstractProvenance::join,
        );
        assert_laws(
            &[
                AbstractByteRange::Exact(range(0, 8)),
                AbstractByteRange::Exact(range(8, 16)),
                AbstractByteRange::Symbolic {
                    start: SymbolicRangeBound::constant(0),
                    end: SymbolicRangeBound::new(
                        AffineExpression::identity(VirValueId::new(9)),
                        U64Interval::new(8, 16).unwrap(),
                    ),
                },
                AbstractByteRange::Unknown,
            ],
            AbstractByteRange::join,
        );
        assert_laws(
            &[
                GuaranteedAlignment::new(1).unwrap(),
                GuaranteedAlignment::new(4).unwrap(),
                GuaranteedAlignment::new(16).unwrap(),
            ],
            GuaranteedAlignment::join,
        );

        let intervals = [
            U64Interval::exact(0),
            U64Interval::new(0, 8).unwrap(),
            U64Interval::new(4, 16).unwrap(),
            U64Interval::unknown(),
        ];
        assert_laws(&intervals, U64Interval::join);

        let permissions = [
            AbstractPermission::new(
                AbstractProvenance::Known(AbstractAllocationId::new(0)),
                AbstractByteRange::Exact(range(0, 8)),
                AccessPermission::Write,
                FreeCapability::Yes,
            ),
            AbstractPermission::new(
                AbstractProvenance::Known(AbstractAllocationId::new(1)),
                AbstractByteRange::Exact(range(8, 16)),
                AccessPermission::Read,
                FreeCapability::No,
            ),
            {
                let mut permission = AbstractPermission::new(
                    AbstractProvenance::Unknown,
                    AbstractByteRange::Unknown,
                    AccessPermission::Write,
                    FreeCapability::Maybe,
                );
                permission.availability = PermissionAvailability::MaybeConsumed;
                permission
            },
        ];
        assert_laws(&permissions, AbstractPermission::join);
    }

    #[test]
    fn resource_join_merges_common_facts_and_drops_path_local_definitions() {
        let allocation_id = AbstractAllocationId::new(0);
        let mut left = ResourceState::new();
        let mut right = ResourceState::new();
        left.define_allocation(allocation_id, allocation(32))
            .unwrap();
        let mut dead = allocation(32);
        dead.mark_dead();
        right.define_allocation(allocation_id, dead).unwrap();

        let pointer_id = VirValueId::new(0);
        left.define_value(
            pointer_id,
            AbstractValue::Pointer(AbstractPointer::new(
                AbstractProvenance::Known(allocation_id),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            )),
        )
        .unwrap();
        right
            .define_value(
                pointer_id,
                AbstractValue::Pointer(AbstractPointer::new(
                    AbstractProvenance::Known(allocation_id),
                    U64Interval::exact(8),
                    GuaranteedAlignment::new(8).unwrap(),
                )),
            )
            .unwrap();
        left.define_value(
            VirValueId::new(9),
            AbstractValue::U64(U64Interval::exact(1)),
        )
        .unwrap();

        let joined = left.join(&right).unwrap();
        assert_eq!(
            joined.allocation(allocation_id).unwrap().liveness(),
            LivenessState::MaybeLive
        );
        assert_eq!(
            joined.allocation(allocation_id).unwrap().ownership(),
            OwnershipState::MaybeOwned
        );
        let Some(AbstractValue::Pointer(pointer)) = joined.value(pointer_id) else {
            panic!("common pointer fact must remain")
        };
        assert_eq!(pointer.offset_bytes(), U64Interval::new(0, 8).unwrap());
        assert!(joined.value(VirValueId::new(9)).is_none());
    }

    #[test]
    fn resource_payload_join_is_atomic_and_never_recreates_a_moved_owner() {
        let allocation_id = AbstractAllocationId::new(7);
        let pointer = AbstractPointer::new(
            AbstractProvenance::Known(allocation_id),
            U64Interval::exact(0),
            GuaranteedAlignment::new(8).unwrap(),
        );
        let permission = AbstractPermission::new(
            AbstractProvenance::Known(allocation_id),
            AbstractByteRange::Exact(range(0, 8)),
            AccessPermission::Write,
            FreeCapability::Yes,
        );
        let available = MovePathState::available(TypedResourcePayload::new(pointer, permission));
        assert_eq!(available.join(&available), available);
        assert_eq!(
            MovePathState::Moved.join(&MovePathState::Moved),
            MovePathState::Moved
        );
        assert_eq!(
            available.join(&MovePathState::Moved),
            MovePathState::Unknown
        );
        assert_eq!(
            MovePathState::Moved.join(&available),
            MovePathState::Unknown
        );

        let other = MovePathState::available(TypedResourcePayload::new(
            AbstractPointer::new(
                AbstractProvenance::Known(AbstractAllocationId::new(8)),
                U64Interval::exact(0),
                GuaranteedAlignment::new(8).unwrap(),
            ),
            permission,
        ));
        assert_eq!(available.join(&other), MovePathState::Unknown);
    }

    #[test]
    fn dynamic_object_offsets_are_bounded_and_canonical() {
        let base = AbstractObjectOffsets::Exact(16);
        let offsets = base.offset_by_index(U64Interval::new(1, 3).unwrap(), 8);
        assert_eq!(offsets.candidates(), Some(vec![24, 32, 40]));
        assert_eq!(
            base.offset_by_index(
                U64Interval::new(
                    0,
                    u64::try_from(VERIFIER_OBJECT_OFFSET_MAX_CANDIDATES).unwrap(),
                )
                .unwrap(),
                8,
            ),
            AbstractObjectOffsets::Unknown
        );
        assert_eq!(
            AbstractObjectOffsets::Exact(8).join(AbstractObjectOffsets::Exact(24)),
            AbstractObjectOffsets::Unknown
        );
    }

    #[test]
    fn resource_join_rejects_inconsistent_immutable_metadata_and_value_kinds() {
        let allocation_id = AbstractAllocationId::new(0);
        let mut left = ResourceState::new();
        let mut right = ResourceState::new();
        left.define_allocation(allocation_id, allocation(8))
            .unwrap();
        right
            .define_allocation(allocation_id, allocation(16))
            .unwrap();
        assert_eq!(
            left.join(&right),
            Err(ResourceJoinError::AllocationSizeMismatch {
                allocation: allocation_id,
            })
        );

        let mut left = ResourceState::new();
        let mut right = ResourceState::new();
        let value = VirValueId::new(0);
        left.define_value(value, AbstractValue::U64(U64Interval::exact(1)))
            .unwrap();
        right
            .define_value(value, AbstractValue::Bool(AbstractBool::True))
            .unwrap();
        assert_eq!(
            left.join(&right),
            Err(ResourceJoinError::ValueKindMismatch { value })
        );
    }

    #[test]
    fn complete_resource_join_obeys_semilattice_laws() {
        fn state(
            initialized: ByteRange,
            liveness: LivenessState,
            ownership: OwnershipState,
            offset: u64,
            path_fact: PathFact,
        ) -> ResourceState {
            let allocation_id = AbstractAllocationId::new(0);
            let mut allocation = allocation(24);
            allocation.mark_initialized(initialized).unwrap();
            allocation.set_liveness(liveness);
            allocation.set_ownership(ownership);

            let mut state = ResourceState::new();
            state.define_allocation(allocation_id, allocation).unwrap();
            state
                .define_value(
                    VirValueId::new(0),
                    AbstractValue::Pointer(AbstractPointer::new(
                        AbstractProvenance::Known(allocation_id),
                        U64Interval::exact(offset),
                        GuaranteedAlignment::new(8).unwrap(),
                    )),
                )
                .unwrap();
            state.conjoin_path_fact(PathFact::boolean(VirValueId::new(1), true));
            state.conjoin_path_fact(path_fact);
            state
        }

        let states = [
            state(
                range(0, 8),
                LivenessState::Live,
                OwnershipState::Owned,
                0,
                PathFact::boolean(VirValueId::new(2), true),
            ),
            state(
                range(8, 16),
                LivenessState::Dead,
                OwnershipState::Unowned,
                8,
                PathFact::boolean(VirValueId::new(3), true),
            ),
            state(
                range(4, 12),
                LivenessState::MaybeLive,
                OwnershipState::MaybeOwned,
                16,
                PathFact::boolean(VirValueId::new(4), true),
            ),
        ];

        for left in &states {
            assert_eq!(left.join(left).unwrap(), *left);
            for right in &states {
                assert_eq!(left.join(right).unwrap(), right.join(left).unwrap());
                for third in &states {
                    assert_eq!(
                        left.join(right).unwrap().join(third).unwrap(),
                        left.join(&right.join(third).unwrap()).unwrap()
                    );
                }
            }
        }
    }

    #[test]
    fn state_definitions_are_unique_and_unreachable_is_join_identity() {
        let mut state = ResourceState::new();
        let allocation_id = AbstractAllocationId::new(0);
        state
            .define_allocation(allocation_id, allocation(8))
            .unwrap();
        assert_eq!(
            state.define_allocation(allocation_id, allocation(16)),
            Err(ResourceStateDefinitionError::DuplicateAllocation(
                allocation_id
            ))
        );
        assert_eq!(
            state
                .allocation(allocation_id)
                .expect("original allocation remains")
                .size_bytes(),
            8
        );

        let value = VirValueId::new(0);
        state
            .define_value(value, AbstractValue::Bool(AbstractBool::True))
            .unwrap();
        assert_eq!(
            state.define_value(value, AbstractValue::Bool(AbstractBool::False)),
            Err(ResourceStateDefinitionError::DuplicateValue(value))
        );
        assert_eq!(
            state.value(value),
            Some(&AbstractValue::Bool(AbstractBool::True))
        );
        assert_eq!(state.join(&ResourceState::unreachable()).unwrap(), state);
    }

    #[test]
    fn allocation_identity_namespaces_and_summary_instances_are_disjoint() {
        let value = VirValueId::new(7);
        let external = AbstractAllocationId::new(value.get());
        let local = AbstractAllocationId::vir_allocation_site(value);
        let frame_local = AbstractAllocationId::vir_local_storage_site(value);
        let first_summary = AbstractAllocationId::contract_instance(3, value.get());
        let second_summary = AbstractAllocationId::contract_instance(4, value.get());
        let entry_payload = AbstractAllocationId::abi_entry_payload(1, 2, value.get());
        let call_payload = AbstractAllocationId::abi_call_payload(3, 0, value.get());

        assert_ne!(external, local);
        assert_ne!(external, first_summary);
        assert_ne!(local, first_summary);
        assert_ne!(external, frame_local);
        assert_ne!(local, frame_local);
        assert_ne!(frame_local, first_summary);
        assert_ne!(first_summary, second_summary);
        assert_ne!(first_summary, entry_payload);
        assert_ne!(entry_payload, call_payload);
        assert_eq!(external.get(), local.get());
        assert_eq!(external.get(), first_summary.get());
        assert_eq!(external.get(), frame_local.get());
        assert_eq!(external.to_string(), "external:7");
        assert_eq!(local.to_string(), "site:%7");
        assert_eq!(frame_local.to_string(), "local-storage:%7");
        assert_eq!(first_summary.to_string(), "summary:3:7");
        assert_eq!(entry_payload.to_string(), "abi-entry:1:2:7");
        assert_eq!(call_payload.to_string(), "abi-call:3:0:7");
    }

    #[test]
    fn affine_expressions_track_scaling_offsets_and_guaranteed_alignment() {
        let root = AffineExpression::identity(VirValueId::new(0));
        let doubled = root.checked_add(root).expect("doubling cannot overflow");
        let scaled = doubled
            .checked_add(doubled)
            .and_then(|value| value.checked_add(value))
            .expect("scaling by eight cannot overflow");
        let advanced = scaled
            .checked_add(AffineExpression::constant(8))
            .expect("small addend cannot overflow");

        assert_eq!(scaled.scale(), 8);
        assert_eq!(scaled.addend(), 0);
        assert_eq!(scaled.guaranteed_alignment().bytes(), 8);
        assert_eq!(advanced.scale(), 8);
        assert_eq!(advanced.addend(), 8);
        assert_eq!(advanced.guaranteed_alignment().bytes(), 8);
        assert_eq!(root.checked_scale(8), Some(scaled));
        assert_eq!(root.checked_scale(0), Some(AffineExpression::constant(0)));
        assert!(
            AffineExpression::constant(u64::MAX)
                .checked_add(AffineExpression::constant(1))
                .is_none()
        );
    }

    #[test]
    fn two_root_affine_budget_and_cfg_projection_drop_missing_terms() {
        let a = AffineExpression::identity(VirValueId::new(0))
            .checked_scale(32)
            .unwrap();
        let b = AffineExpression::identity(VirValueId::new(1))
            .checked_scale(8)
            .unwrap();
        let sum = a.checked_add(b).unwrap();
        assert_eq!(sum, b.checked_add(a).unwrap());
        assert!(!sum.is_constant());
        assert_eq!(sum.root(), None);
        assert_eq!(sum.guaranteed_alignment().bytes(), 8);
        assert!(
            sum.checked_add(AffineExpression::identity(VirValueId::new(2)))
                .is_none()
        );
        assert!(sum.checked_scale(u64::MAX).is_none());
        assert!(
            sum.rename_root(&BTreeMap::from([(VirValueId::new(0), VirValueId::new(10))]))
                .is_none()
        );
        let renamed = sum
            .rename_root(&BTreeMap::from([
                (VirValueId::new(0), VirValueId::new(10)),
                (VirValueId::new(1), VirValueId::new(10)),
            ]))
            .unwrap();
        assert_eq!(
            renamed,
            AffineExpression::identity(VirValueId::new(10))
                .checked_scale(40)
                .unwrap()
        );
        let mut state = ResourceState::new();
        for id in 0..2 {
            state
                .define_value(
                    VirValueId::new(id),
                    AbstractValue::U64(U64Interval::new(0, 2).unwrap()),
                )
                .unwrap();
        }
        let range = AbstractByteRange::from_bounds(
            SymbolicRangeBound::new(sum, U64Interval::new(0, 80).unwrap()),
            SymbolicRangeBound::new(
                sum.checked_add_constant(8).unwrap(),
                U64Interval::new(8, 88).unwrap(),
            ),
        );
        let partial = ExpressionRemapper::new(&state, &[(VirValueId::new(0), VirValueId::new(10))]);
        assert_eq!(partial.range(range), AbstractByteRange::Unknown);
        let complete = ExpressionRemapper::new(
            &state,
            &[
                (VirValueId::new(0), VirValueId::new(10)),
                (VirValueId::new(1), VirValueId::new(11)),
            ],
        );
        assert_ne!(complete.range(range), AbstractByteRange::Unknown);
    }

    #[test]
    fn cfg_projection_renames_symbols_inside_permissions() {
        let source_word = VirValueId::new(0);
        let source_permission = VirValueId::new(1);
        let target_word = VirValueId::new(10);
        let target_permission = VirValueId::new(11);
        let expression = AffineExpression::identity(source_word);
        let mut state = ResourceState::new();
        state
            .define_value(
                source_word,
                AbstractValue::U64(U64Interval::new(8, 24).unwrap()),
            )
            .unwrap();
        state.set_word_expression(source_word, expression);
        state
            .define_value(
                source_permission,
                AbstractValue::Permission(AbstractPermission::new(
                    AbstractProvenance::Known(AbstractAllocationId::new(0)),
                    AbstractByteRange::Symbolic {
                        start: SymbolicRangeBound::constant(0),
                        end: SymbolicRangeBound::new(expression, U64Interval::new(8, 24).unwrap()),
                    },
                    AccessPermission::Write,
                    FreeCapability::No,
                )),
            )
            .unwrap();
        let renames = [
            (source_word, target_word),
            (source_permission, target_permission),
        ];

        let projected = state.project_cfg_edge(&renames);
        assert_eq!(
            projected.word_expression(target_word),
            Some(AffineExpression::identity(target_word))
        );
        let Some(AbstractValue::Permission(permission)) =
            state.project_value_for_cfg(source_permission, &renames)
        else {
            panic!("permission must project")
        };
        let AbstractByteRange::Symbolic { end, .. } = permission.range() else {
            panic!("symbolic range must be retained")
        };
        assert_eq!(end.expression(), AffineExpression::identity(target_word));
    }

    #[test]
    fn footprint_projection_renames_pointer_loan_and_stored_payload_together() {
        let source = VirValueId::new(0);
        let authority = VirValueId::new(1);
        let target = VirValueId::new(10);
        let target_authority = VirValueId::new(11);
        let storage = AbstractAllocationId::new(0);
        let provenance = AbstractProvenance::Known(storage);
        let access = VirMemoryAccess::core_u64();
        let start = SymbolicRangeBound::new(
            AffineExpression::identity(source),
            U64Interval::new(0, 8).unwrap(),
        );
        let footprint = MemoryFootprint {
            provenance,
            access,
            stride_bytes: 8,
            range: AbstractByteRange::from_bounds(start, start.checked_add_constant(8).unwrap()),
            envelope: range(0, 16),
        };
        let pointer = AbstractPointer::new(
            provenance,
            start.interval(),
            GuaranteedAlignment::new(8).unwrap(),
        )
        .with_offset_expression(Some(start.expression()))
        .with_memory_access(Some(access))
        .with_slice_footprint(Some(footprint));
        let id = VirLoanId::new(0);
        let permission = AbstractPermission::new(
            provenance,
            footprint.range,
            AccessPermission::Read,
            FreeCapability::No,
        )
        .with_authority(PermissionAuthority::Loan(id));
        let key = ResourcePayloadKey::new(0, access);
        let mut allocation = allocation(16);
        allocation
            .set_resource_payload(
                key,
                MovePathState::available(TypedResourcePayload::new(pointer, permission)),
            )
            .unwrap();
        let mut state = ResourceState::new();
        state.define_allocation(storage, allocation).unwrap();
        state
            .define_value(source, AbstractValue::U64(start.interval()))
            .unwrap();
        state
            .define_value(authority, AbstractValue::Permission(permission))
            .unwrap();
        state
            .define_loan(
                id,
                AbstractLoan::new(
                    provenance,
                    footprint.envelope,
                    VirLoanKind::Shared,
                    VirBorrowRegionId::new(0),
                    None,
                    LoanActivity::Active,
                )
                .with_footprint(Some(footprint))
                .with_authority(authority),
            )
            .unwrap();
        for keep_symbol in [true, false] {
            let mut renames = vec![(authority, target_authority)];
            if keep_symbol {
                renames.push((source, target));
            }
            let remapper = ExpressionRemapper::new(&state, &renames);
            let projected = state.project_cfg_edge(&renames);
            let loan = projected.loan(id).unwrap();
            assert_eq!(loan.activity(), LoanActivity::Active);
            assert_eq!(loan.range(), footprint.envelope);
            assert!(loan.has_value_authority(target_authority));
            let selected = remapper.pointer(pointer).slice_footprint().unwrap();
            assert_eq!(selected.range, loan.actual_range());
            let MovePathState::Available(payload) =
                projected.allocation(storage).unwrap().resource_payload(key)
            else {
                panic!("payload must survive")
            };
            assert_eq!(payload.pointer().slice_footprint(), Some(selected));
            assert_eq!(payload.permission().range(), selected.range);
            if keep_symbol {
                assert_eq!(
                    selected.range.bounds().unwrap().0.expression().root(),
                    Some(target)
                );
            } else {
                assert_eq!(selected.range, AbstractByteRange::Unknown);
            }
        }
    }

    #[test]
    fn footprint_join_and_widen_never_promote_an_envelope_to_authority() {
        let id = VirLoanId::new(0);
        let envelope = range(0, 32);
        let provenance = AbstractProvenance::Known(AbstractAllocationId::new(0));
        let base = AbstractLoan::new(
            provenance,
            envelope,
            VirLoanKind::Shared,
            VirBorrowRegionId::new(0),
            None,
            LoanActivity::Active,
        );
        assert_eq!(base.actual_range(), AbstractByteRange::Unknown);
        let footprint = MemoryFootprint {
            provenance,
            access: VirMemoryAccess::core_u64(),
            stride_bytes: 8,
            range: AbstractByteRange::Exact(range(8, 16)),
            envelope,
        };
        let left = base.clone().with_footprint(Some(footprint));
        for other in [
            None,
            Some(MemoryFootprint {
                range: AbstractByteRange::Exact(range(16, 24)),
                ..footprint
            }),
            Some(MemoryFootprint {
                stride_bytes: 4,
                ..footprint
            }),
        ] {
            let right = base.clone().with_footprint(other);
            let mut a = ResourceState::new();
            let mut b = ResourceState::new();
            a.define_loan(id, left.clone()).unwrap();
            b.define_loan(id, right).unwrap();
            for joined in [a.join(&b).unwrap(), a.widen(&b).unwrap()] {
                let loan = joined.loan(id).unwrap();
                assert_eq!(loan.range(), envelope);
                assert_eq!(loan.actual_range(), AbstractByteRange::Unknown);
                assert_eq!(loan.activity(), LoanActivity::Active);
            }
        }
    }

    #[test]
    fn invalid_ranges_intervals_allocations_and_alignments_fail_closed() {
        assert!(matches!(
            ByteRange::new(2, 1),
            Err(ByteRangeError::Reversed { .. })
        ));
        assert!(matches!(
            ByteRange::from_start_and_length(u64::MAX, 1),
            Err(ByteRangeError::EndOverflow { .. })
        ));
        assert!(U64Interval::new(2, 1).is_err());
        assert!(GuaranteedAlignment::new(3).is_err());
        assert_eq!(
            AbstractAllocation::new(VirRegionId::new(0), 0, 8),
            Err(AbstractAllocationError::ZeroSize)
        );
    }
}
