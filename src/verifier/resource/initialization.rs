//! Bounded relational initialization facts, inferred by ordinary instruction
//! transfer and intersected at every CFG join. No source loop annotations are
//! trusted and no runtime iteration is unrolled to establish the invariant.

use super::*;
use crate::{VirIntegerType, VirMemoryAccess, VirMemorySchema, VirMemoryTypeKind, VirObjectShape};

mod partition;
#[cfg(test)]
mod range_tests;

const MAX_PREFIXES: usize = 64;
const MAX_EQUIVALENT_COUNTS: usize = 16;
const MAX_PREFIX_RELATION_QUERIES: usize = 256;

/// Every fact denotes valid, initialized scalar elements [begin, cursor) at one
/// canonical allocation-relative array. No padding, tags or resource authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ArrayKey {
    base: u64,
    stride: u64,
    length: u64,
    element: VirMemoryAccess,
    begin: AffineExpression,
}

impl ArrayKey {
    fn extent(self) -> Option<ByteRange> {
        ByteRange::from_start_and_length(self.base, self.stride.checked_mul(self.length)?).ok()
    }

    fn fully_materialized(self, allocation: &AbstractAllocation) -> bool {
        self.extent().is_some_and(|range| {
            allocation.initialization().classify(range) == InitializationClass::Initialized
                && allocation.valid_value_bytes().contains(range)
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub(super) struct InitializationPrefixes {
    facts: BTreeMap<ArrayKey, BTreeSet<AffineExpression>>,
}

impl InitializationPrefixes {
    pub(super) fn invalidate(&mut self, range: ByteRange) {
        for (key, counts) in &mut self.facts {
            if key.extent().is_none_or(|extent| overlaps(extent, range)) {
                *counts = BTreeSet::from([key.begin]);
            }
        }
    }

    pub(super) fn join(&self, other: &Self) -> Self {
        Self {
            facts: self
                .facts
                .iter()
                .filter_map(|(key, counts)| {
                    let other = other.facts.get(key)?;
                    Some((*key, counts.intersection(other).copied().collect()))
                })
                .collect(),
        }
    }

    pub(super) fn project(
        &self,
        remapper: &ExpressionRemapper,
        values: &BTreeMap<VirValueId, AbstractValue>,
    ) -> Self {
        let mut result = Self::default();
        for (key, counts) in &self.facts {
            let Some(begin) = remapper.expression(key.begin).or_else(|| {
                interval(key.begin, values)
                    .and_then(U64Interval::exact_value)
                    .map(AffineExpression::constant)
            }) else {
                continue;
            };
            let mut projected = BTreeSet::from([begin]);
            let mut normalized = counts.clone();
            for count in counts {
                if let Some(value) = interval(*count, values).and_then(U64Interval::exact_value) {
                    normalized.insert(AffineExpression::constant(value));
                }
            }
            for count in &normalized {
                if let Some(count) = remapper.expression(*count) {
                    projected.insert(count);
                }
                // A constant prefix at loop entry is equal to every matching
                // scalar edge argument, not just the first duplicate zero.
                // Keeping all bounded equalities allows the back edge to pick
                // the actual induction parameter by intersection.
                for (expression, target) in &remapper.prefix_expressions {
                    if count == expression {
                        projected.insert(AffineExpression::identity(*target));
                    }
                    // The first latch can carry i=0 and prefix=1. Normalize
                    // that equality to prefix=i+1 before joining it with later
                    // symbolic iterations; numeric equality is evidence only
                    // on this predecessor, never an assumption at the join.
                    if count.same_terms(*expression)
                        && let Some(delta) = count.addend().checked_sub(expression.addend())
                        && let Some(affine) =
                            AffineExpression::identity(*target).checked_add_constant(delta)
                    {
                        projected.insert(affine);
                    }
                }
            }
            limit_counts_from(&mut projected, begin);
            // Two origins may become the same SSA expression on this edge.
            // Both sets are established on this predecessor, so union here is
            // sound; predecessor joins below still use intersection only.
            let destination = result.facts.entry(ArrayKey { begin, ..*key }).or_default();
            destination.extend(projected);
            limit_counts_from(destination, begin);
        }
        result
    }
}

fn empty_prefix() -> BTreeSet<AffineExpression> {
    BTreeSet::from([AffineExpression::constant(0)])
}

#[cfg(test)]
fn limit_counts(counts: &mut BTreeSet<AffineExpression>) {
    limit_counts_from(counts, AffineExpression::constant(0));
}

fn limit_counts_from(counts: &mut BTreeSet<AffineExpression>, begin: AffineExpression) {
    if counts.len() > MAX_EQUIVALENT_COUNTS {
        *counts = BTreeSet::from([begin]);
    }
}

fn overlaps(left: ByteRange, right: ByteRange) -> bool {
    left.start() < right.end() && right.start() < left.end()
}

fn interval(
    expression: AffineExpression,
    values: &BTreeMap<VirValueId, AbstractValue>,
) -> Option<U64Interval> {
    let root = match expression.root() {
        Some(id) => match values.get(&id)? {
            AbstractValue::U64(value) => *value,
            _ => return None,
        },
        None if expression.is_constant() => U64Interval::exact(0),
        None => return None,
    };
    // The lower bound is sufficient for reduction; an overflowing abstract
    // upper bound loses precision rather than inventing a wrapping count.
    U64Interval::new(
        root.lower()
            .checked_mul(expression.scale())?
            .checked_add(expression.addend())?,
        root.upper()
            .checked_mul(expression.scale())
            .and_then(|value| value.checked_add(expression.addend()))
            .unwrap_or(u64::MAX),
    )
    .ok()
}

impl AbstractAllocation {
    pub(crate) fn seed_initialization_prefixes(
        &mut self,
        memory: &VirMemorySchema,
        shape: &VirObjectShape,
    ) {
        if !shape.variants().is_empty() {
            return;
        }
        for array in shape.arrays() {
            let element = array.element_access();
            if !matches!(
                memory.kind(element.ty),
                Some(
                    VirMemoryTypeKind::Bool
                        | VirMemoryTypeKind::Integer(VirIntegerType::U64 | VirIntegerType::Usize)
                )
            ) {
                continue;
            }
            let key = ArrayKey {
                base: array.extent().start_bytes(),
                stride: array.stride_bytes(),
                length: array.length(),
                element,
                begin: AffineExpression::constant(0),
            };
            if key.stride == 0
                || key
                    .extent()
                    .is_none_or(|range| range.end() > self.size_bytes)
            {
                continue;
            }
            if self.initialization_prefixes.facts.len() >= MAX_PREFIXES {
                break;
            }
            self.initialization_prefixes
                .facts
                .insert(key, empty_prefix());
        }
    }
}

impl ResourceState {
    /// Only facts whose scalar roots are syntactically unchanged survive an
    /// inner induction cut. Actual scalar writes preserve their valid bytes.
    pub(in crate::verifier) fn inherit_loop_initialization_frame(
        &mut self,
        entry: &Self,
        retained: &BTreeSet<VirValueId>,
    ) {
        let stable = |e: AffineExpression| {
            e.terms()
                .into_iter()
                .flatten()
                .all(|(id, _)| retained.contains(&id))
        };
        for (id, before) in &entry.allocations {
            let Some(after) = self.allocations.get_mut(id) else {
                continue;
            };
            after.initialization_prefixes.facts = before
                .initialization_prefixes
                .facts
                .iter()
                .filter(|(key, _)| stable(key.begin))
                .map(|(key, counts)| {
                    (
                        *key,
                        counts.iter().copied().filter(|e| stable(*e)).collect(),
                    )
                })
                .collect();
        }
    }
    /// Provisional loop-local initialization, guarded by entry/backedge proof.
    /// Caller has checked geometry and matched the existing live instance.
    /// This creates neither allocation nor authority.
    pub(in crate::verifier) fn assume_loop_initialized(
        &mut self,
        pointer: AbstractPointer,
        element: VirMemoryAccess,
        bounds: (AffineExpression, AffineExpression),
        stride: u64,
        length: u64,
    ) -> bool {
        let AbstractProvenance::Known(id) = pointer.provenance() else {
            return false;
        };
        let Some(base) = pointer.offset_bytes().exact_value() else {
            return false;
        };
        let index = |e: AffineExpression| {
            if stride == 0
                || !e.scale().is_multiple_of(stride)
                || !e.addend().is_multiple_of(stride)
                || (!e.is_constant() && e.root().is_none())
            {
                return None;
            }
            Some(AffineExpression {
                root: e.root(),
                scale: e.scale() / stride,
                addend: e.addend() / stride,
                second: None,
            })
        };
        let (Some(begin), Some(cursor)) = (index(bounds.0), index(bounds.1)) else {
            return false;
        };
        let key = ArrayKey {
            base,
            stride,
            length,
            element,
            begin,
        };
        let Some(allocation) = self.allocations.get_mut(&id) else {
            return false;
        };
        if allocation.liveness() != LivenessState::Live
            || key
                .extent()
                .is_none_or(|r| r.end() > allocation.size_bytes())
            || allocation.initialization_prefixes.facts.len() >= MAX_PREFIXES
                && !allocation.initialization_prefixes.facts.contains_key(&key)
        {
            return false;
        }
        let counts = allocation
            .initialization_prefixes
            .facts
            .entry(key)
            .or_default();
        if counts.len() >= MAX_EQUIVALENT_COUNTS {
            return false;
        }
        counts.insert(cursor);
        true
    }

    /// Query established scalar-prefix facts without materializing the access
    /// envelope as initialized bytes. Numeric containment supplies neither
    /// authority nor liveness; those remain independent transfer obligations.
    pub(crate) fn initialized_prefix_covers(
        &self,
        allocation: AbstractAllocationId,
        access: VirMemoryAccess,
        range: AbstractByteRange,
        limits: DifferenceLimits,
        queries: &super::super::relation::audit::QueryLog,
    ) -> bool {
        for partition in self
            .initialization_partitions(allocation, access)
            .into_iter()
            .take(MAX_PREFIX_RELATION_QUERIES)
        {
            if queries
                .contained(self, partition.initialized, range, limits)
                .is_proven()
            {
                return true;
            }
        }
        false
    }

    /// Export only proved lower prefixes to edge arguments before the loop
    /// induction root disappears. In particular, the exit condition n <= i
    /// and an established [0,i) prefix justify [0,n), without assuming i=n.
    pub(crate) fn project_initialization_prefix_relations(
        &self,
        renames: &[(VirValueId, VirValueId)],
        projected: &mut Self,
        limits: DifferenceLimits,
        queries: &super::super::relation::audit::QueryLog,
        seed_empty: bool,
    ) {
        let mut count_queries = 0;
        let remapper = ExpressionRemapper::new(self, renames);
        for (id, allocation) in &self.allocations {
            if allocation.liveness() != LivenessState::Live {
                continue;
            }
            for (key, counts) in &allocation.initialization_prefixes.facts {
                // Ordinary byte facts already cover every element. Additional
                // relational candidates are redundant (especially for updates
                // to nested fully-constructed arrays with many scalar inputs).
                if key.fully_materialized(allocation) {
                    continue;
                }
                let Some(begin) = remapper.expression(key.begin).or_else(|| {
                    interval(key.begin, &self.values)
                        .and_then(U64Interval::exact_value)
                        .map(AffineExpression::constant)
                }) else {
                    continue;
                };
                let projected_key = ArrayKey { begin, ..*key };
                for &(source, target) in renames {
                    let Some(AbstractValue::U64(value)) = self.value(source) else {
                        continue;
                    };
                    if value.upper() > key.length {
                        continue;
                    }
                    // An empty interval is true at any in-bounds index. Seed
                    // it on actual edges, not from a source invariant. This
                    // lets a nonzero/dynamic start survive the zero-iteration
                    // predecessor without granting initialized bytes.
                    if seed_empty
                        && key.begin == AffineExpression::constant(0)
                        && let Some(destination) = projected.allocations.get_mut(id)
                    {
                        for begin in [
                            Some(AffineExpression::identity(source)),
                            value.exact_value().map(AffineExpression::constant),
                        ]
                        .into_iter()
                        .flatten()
                        {
                            let empty = InitializationPrefixes {
                                facts: BTreeMap::from([(
                                    ArrayKey { begin, ..*key },
                                    BTreeSet::from([begin]),
                                )]),
                            }
                            .project(&remapper, &self.values);
                            for (empty_key, aliases) in empty.facts {
                                let facts = &mut destination.initialization_prefixes.facts;
                                if facts.contains_key(&empty_key) || facts.len() < MAX_PREFIXES {
                                    let counts = facts.entry(empty_key).or_default();
                                    for alias in aliases {
                                        if counts.len() < MAX_EQUIVALENT_COUNTS {
                                            counts.insert(alias);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // Structural projection already retained this conclusion.
                    // Do not replay every alias through the numeric solver.
                    if projected
                        .allocations
                        .get(id)
                        .and_then(|a| a.initialization_prefixes.facts.get(&projected_key))
                        .is_some_and(|counts| counts.contains(&AffineExpression::identity(target)))
                        || counts.iter().all(|count| *count == key.begin)
                    {
                        continue;
                    }
                    let Some(start) = interval(key.begin, &self.values) else {
                        continue;
                    };
                    count_queries += 1;
                    if count_queries > MAX_PREFIX_RELATION_QUERIES {
                        return;
                    }
                    if !queries
                        .ordered(
                            self,
                            SymbolicRangeBound::new(key.begin, start),
                            SymbolicRangeBound::new(AffineExpression::identity(source), *value),
                            limits,
                        )
                        .is_proven()
                    {
                        continue;
                    }
                    for count in counts {
                        let Some(bound) = interval(*count, &self.values) else {
                            continue;
                        };
                        count_queries += 1;
                        if count_queries > MAX_PREFIX_RELATION_QUERIES {
                            return;
                        }
                        if queries
                            .ordered(
                                self,
                                SymbolicRangeBound::new(AffineExpression::identity(source), *value),
                                SymbolicRangeBound::new(*count, bound),
                                limits,
                            )
                            .is_proven()
                        {
                            let Some(destination) =
                                projected.allocations.get_mut(id).and_then(|a| {
                                    a.initialization_prefixes.facts.get_mut(&projected_key)
                                })
                            else {
                                continue;
                            };
                            // Preserve existing facts at capacity; additional
                            // exports are optional precision, not new writes.
                            if destination.len() < MAX_EQUIVALENT_COUNTS {
                                destination.insert(AffineExpression::identity(target));
                            }
                            break;
                        }
                    }
                }
            }
        }
    }

    /// Reduce a symbolic prefix to a single definite byte interval using only
    /// the current SSA lower bound. Called before observations and before SSA
    /// projection can discard the induction variable on a loop exit.
    pub(crate) fn reduce_initialization_prefixes(&mut self) {
        for allocation in self.allocations.values_mut() {
            allocation.reduce_initialization_prefixes(&self.values);
        }
    }

    /// Called only after all obligations of a typed scalar write are Proven.
    /// A valid update preserves an existing prefix. A write exactly at its
    /// frontier advances it by one; skips, bad strides and wrapping arithmetic
    /// cannot satisfy that equality.
    pub(crate) fn advance_initialization_prefixes(
        &mut self,
        before: &AbstractAllocation,
        pointer: AbstractPointer,
        access: VirMemoryAccess,
        limits: DifferenceLimits,
        queries: &super::super::relation::audit::QueryLog,
    ) {
        let AbstractProvenance::Known(id) = pointer.provenance() else {
            return;
        };
        if before.liveness() != LivenessState::Live || !self.allocations.contains_key(&id) {
            return;
        }
        let mut changes = BTreeMap::new();
        let mut covered_arrays = BTreeSet::new();
        let mut count_queries = 0;
        for (key, counts) in &before.initialization_prefixes.facts {
            if key.element != access || key.fully_materialized(before) {
                continue;
            }
            let Some(offset) = pointer.offset_expression().or_else(|| {
                pointer
                    .offset_bytes()
                    .exact_value()
                    .map(AffineExpression::constant)
            }) else {
                continue;
            };
            let Some(relative) = offset.addend().checked_sub(key.base) else {
                continue;
            };
            if (!offset.is_constant() && offset.root().is_none())
                || offset.scale() % key.stride != 0
                || relative % key.stride != 0
            {
                continue;
            }
            let index = AffineExpression {
                root: offset.root(),
                scale: offset.scale() / key.stride,
                addend: relative / key.stride,
                second: None,
            };
            let Some(indices) = interval(index, &self.values) else {
                continue;
            };
            if indices.upper() >= key.length {
                continue;
            }
            let mut after = counts.clone();
            // Retain the original identity/exact-value fast path. Relational
            // queries are needed only for a genuinely different symbolic root.
            let mut adjacent = counts.iter().any(|count| {
                *count == index
                    || interval(*count, &self.values)
                        .and_then(U64Interval::exact_value)
                        .zip(indices.exact_value())
                        .is_some_and(|(a, b)| a == b)
            });
            for count in counts {
                if adjacent {
                    break;
                }
                let Some(bound) = interval(*count, &self.values) else {
                    continue;
                };
                // Disjoint numeric intervals cannot be adjacent. This is
                // candidate rejection, not unrecorded positive evidence.
                if bound.intersection(indices).is_none() {
                    continue;
                }
                if count_queries + 2 > MAX_PREFIX_RELATION_QUERIES {
                    break;
                }
                count_queries += 2;
                let a = SymbolicRangeBound::new(*count, bound);
                let b = SymbolicRangeBound::new(index, indices);
                if queries.ordered(self, a, b, limits).is_proven()
                    && queries.ordered(self, b, a, limits).is_proven()
                {
                    adjacent = true;
                    break;
                }
            }
            if adjacent && let Some(next) = index.checked_add_constant(1) {
                after.insert(next);
                covered_arrays.insert(ArrayKey {
                    begin: AffineExpression::constant(0),
                    ..*key
                });
            }
            limit_counts_from(&mut after, key.begin);
            changes.insert(*key, after);
            // A successful non-frontier write establishes just its own
            // singleton, never the skipped gap. Existing adjacent prefixes
            // were advanced above; no union across predecessors is involved.
            if let Some(next) = index.checked_add_constant(1) {
                changes
                    .entry(ArrayKey {
                        begin: index,
                        ..*key
                    })
                    .or_insert_with(|| BTreeSet::from([index, next]));
            }
        }
        let allocation = self.allocations.get_mut(&id).expect("tracked above");
        // Restore established keys first. Optional singleton precision must
        // not evict an existing inductive prefix at the key budget.
        for (key, counts) in changes {
            if !before.initialization_prefixes.facts.contains_key(&key)
                && covered_arrays.contains(&ArrayKey {
                    begin: AffineExpression::constant(0),
                    ..key
                })
            {
                // An existing prefix already proves this write; do not keep
                // a redundant singleton for every initialized element.
                continue;
            }
            if allocation.initialization_prefixes.facts.contains_key(&key)
                || allocation.initialization_prefixes.facts.len() < MAX_PREFIXES
            {
                allocation.initialization_prefixes.facts.insert(key, counts);
            }
        }
    }
}

impl AbstractAllocation {
    pub(super) fn reduce_initialization_prefixes(
        &mut self,
        values: &BTreeMap<VirValueId, AbstractValue>,
    ) {
        if self.liveness != LivenessState::Live {
            return;
        }
        for (key, counts) in &self.initialization_prefixes.facts {
            let Some(begin) = interval(key.begin, values)
                .and_then(|value| value.upper().checked_mul(key.stride))
                .and_then(|offset| key.base.checked_add(offset))
            else {
                continue;
            };
            let count = counts
                .iter()
                .filter_map(|count| interval(*count, values))
                .map(|value| value.lower())
                .max()
                .unwrap_or(0)
                .min(key.length);
            let Some(end) = count
                .checked_mul(key.stride)
                .and_then(|size| key.base.checked_add(size))
            else {
                continue;
            };
            let Ok(range) = ByteRange::new(begin, end) else {
                continue;
            };
            if range.is_empty() || end > self.size_bytes {
                continue;
            }
            // Reduce established relational facts without invalidating them.
            self.initialization.mark_initialized(range);
            self.valid_value_bytes.insert(range);
        }
    }
}

#[cfg(test)]
mod tests;
