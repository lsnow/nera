//! Bounded relational initialization facts, inferred by ordinary instruction
//! transfer and intersected at every CFG join. No source loop annotations are
//! trusted and no runtime iteration is unrolled to establish the invariant.

use super::*;
use crate::{VirIntegerType, VirMemoryAccess, VirMemorySchema, VirMemoryTypeKind, VirObjectShape};

const MAX_PREFIXES: usize = 64;
const MAX_EQUIVALENT_COUNTS: usize = 16;
const MAX_PREFIX_RELATION_QUERIES: usize = 256;

/// Every fact denotes valid, initialized scalar elements [0, count) at one
/// canonical allocation-relative array. No padding, tags or resource authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ArrayKey {
    base: u64,
    stride: u64,
    length: u64,
    element: VirMemoryAccess,
}

impl ArrayKey {
    fn extent(self) -> Option<ByteRange> {
        ByteRange::from_start_and_length(self.base, self.stride.checked_mul(self.length)?).ok()
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
                *counts = empty_prefix();
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
            let mut projected = empty_prefix();
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
            limit_counts(&mut projected);
            result.facts.insert(*key, projected);
        }
        result
    }
}

fn empty_prefix() -> BTreeSet<AffineExpression> {
    BTreeSet::from([AffineExpression::constant(0)])
}

fn limit_counts(counts: &mut BTreeSet<AffineExpression>) {
    if counts.len() > MAX_EQUIVALENT_COUNTS {
        *counts = empty_prefix();
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
        let Some(allocation) = self.allocation(allocation) else {
            return false;
        };
        if allocation.liveness() != LivenessState::Live {
            return false;
        }
        let mut count_queries = 0;
        for (key, counts) in &allocation.initialization_prefixes.facts {
            if key.element != access {
                continue;
            }
            for count in counts {
                let Some(indices) = interval(*count, &self.values) else {
                    continue;
                };
                if indices.upper() > key.length {
                    continue;
                }
                let Some(end) = count
                    .checked_scale(key.stride)
                    .and_then(|e| e.checked_add_constant(key.base))
                else {
                    continue;
                };
                let Some(bytes) = end.interval(|id| match self.value(id)? {
                    AbstractValue::U64(value) => Some(*value),
                    _ => None,
                }) else {
                    continue;
                };
                let prefix = AbstractByteRange::from_bounds(
                    SymbolicRangeBound::constant(key.base),
                    SymbolicRangeBound::new(end, bytes),
                );
                count_queries += 1;
                if count_queries > MAX_PREFIX_RELATION_QUERIES {
                    return false;
                }
                if queries.contained(self, prefix, range, limits).is_proven() {
                    return true;
                }
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
    ) {
        let mut count_queries = 0;
        for (id, allocation) in &self.allocations {
            if allocation.liveness() != LivenessState::Live {
                continue;
            }
            for (key, counts) in &allocation.initialization_prefixes.facts {
                for &(source, target) in renames {
                    let Some(AbstractValue::U64(value)) = self.value(source) else {
                        continue;
                    };
                    if value.upper() > key.length {
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
                            let Some(destination) = projected
                                .allocations
                                .get_mut(id)
                                .and_then(|a| a.initialization_prefixes.facts.get_mut(key))
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
    ) {
        let AbstractProvenance::Known(id) = pointer.provenance() else {
            return;
        };
        let Some(allocation) = self.allocations.get_mut(&id) else {
            return;
        };
        for (key, counts) in &before.initialization_prefixes.facts {
            if key.element != access {
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
            if counts.iter().any(|count| {
                *count == index
                    || interval(*count, &self.values)
                        .and_then(U64Interval::exact_value)
                        .zip(indices.exact_value())
                        .is_some_and(|(a, b)| a == b)
            }) && let Some(next) = index.checked_add_constant(1)
            {
                after.insert(next);
            }
            limit_counts(&mut after);
            allocation.initialization_prefixes.facts.insert(*key, after);
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
            let Ok(range) = ByteRange::new(key.base, end) else {
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
mod tests {
    use super::*;

    fn key() -> ArrayKey {
        ArrayKey {
            base: 8,
            stride: 8,
            length: 4,
            element: VirMemoryAccess::core_u64(),
        }
    }

    #[test]
    fn relational_prefix_queries_match_a_concrete_byte_oracle_without_mutating_state() {
        let n = VirValueId::new(0);
        let j = VirValueId::new(1);
        let id = AbstractAllocationId::new(0);
        for predicate in [
            VirIntegerPredicate::LessThan,
            VirIntegerPredicate::LessOrEqual,
            VirIntegerPredicate::NotEqual,
        ] {
            let mut state = ResourceState::new();
            state
                .define_value(n, AbstractValue::U64(U64Interval::new(1, 4).unwrap()))
                .unwrap();
            state
                .define_value(j, AbstractValue::U64(U64Interval::new(0, 3).unwrap()))
                .unwrap();
            state.conjoin_path_fact(PathFact::comparison(predicate, j, n));
            let mut allocation = AbstractAllocation::new_local(40, 8).unwrap();
            allocation.initialization_prefixes = prefixes([AffineExpression::identity(n)]);
            state.define_allocation(id, allocation).unwrap();
            for width in [0, 8, 16] {
                let start = SymbolicRangeBound::new(
                    AffineExpression::identity(j)
                        .checked_scale(8)
                        .unwrap()
                        .checked_add_constant(8)
                        .unwrap(),
                    U64Interval::new(8, 32).unwrap(),
                );
                let range = AbstractByteRange::from_bounds(
                    start,
                    start.checked_add_constant(width).unwrap(),
                );
                let before = state.clone();
                let proven = state.initialized_prefix_covers(
                    id,
                    key().element,
                    range,
                    Default::default(),
                    &Default::default(),
                );
                assert_eq!(state, before);
                if predicate == VirIntegerPredicate::LessThan && width <= 8 {
                    assert!(proven);
                }
                for count in 1..=4 {
                    for index in 0..4 {
                        let premise = match predicate {
                            VirIntegerPredicate::LessThan => index < count,
                            VirIntegerPredicate::LessOrEqual => index <= count,
                            _ => index != count,
                        };
                        if premise && proven {
                            assert!(8 + 8 * index + width <= 8 + 8 * count);
                        }
                    }
                }
            }
            let range = AbstractByteRange::Exact(ByteRange::new(8, 16).unwrap());
            assert!(state.initialized_prefix_covers(
                id,
                key().element,
                range,
                Default::default(),
                &Default::default()
            ));
            state
                .allocation_mut(id)
                .unwrap()
                .forget_validity(ByteRange::new(8, 16).unwrap())
                .unwrap();
            assert!(!state.initialized_prefix_covers(
                id,
                key().element,
                range,
                Default::default(),
                &Default::default()
            ));
        }
    }

    #[test]
    fn edge_prefix_export_requires_a_relation_on_that_predecessor() {
        let i = VirValueId::new(0);
        let n = VirValueId::new(1);
        let target = VirValueId::new(2);
        let id = AbstractAllocationId::new(0);
        let mut state = ResourceState::new();
        for value in [i, n] {
            state
                .define_value(value, AbstractValue::U64(U64Interval::new(0, 4).unwrap()))
                .unwrap();
        }
        let mut allocation = AbstractAllocation::new_local(40, 8).unwrap();
        allocation.initialization_prefixes = prefixes([AffineExpression::identity(i)]);
        state.define_allocation(id, allocation).unwrap();
        let renames = [(n, target)];
        let project = |state: &ResourceState| {
            let mut projected = state.project_cfg_edge(&renames);
            state.project_initialization_prefix_relations(
                &renames,
                &mut projected,
                Default::default(),
                &Default::default(),
            );
            projected
        };
        let missing = project(&state);
        assert!(
            !missing.allocations[&id].initialization_prefixes.facts[&key()]
                .contains(&AffineExpression::identity(target))
        );
        state.conjoin_path_fact(PathFact::comparison(VirIntegerPredicate::LessOrEqual, n, i));
        let proved = project(&state);
        assert!(
            proved.allocations[&id].initialization_prefixes.facts[&key()]
                .contains(&AffineExpression::identity(target))
        );
        let joined = proved.join(&missing).unwrap();
        assert!(
            !joined.allocations[&id].initialization_prefixes.facts[&key()]
                .contains(&AffineExpression::identity(target))
        );
    }

    fn prefixes(counts: impl IntoIterator<Item = AffineExpression>) -> InitializationPrefixes {
        InitializationPrefixes {
            facts: BTreeMap::from([(key(), counts.into_iter().collect())]),
        }
    }

    #[test]
    fn joins_keep_only_predecessor_independent_facts() {
        for a in 0..=4 {
            for b in 0..=4 {
                let left = prefixes((0..=a).map(AffineExpression::constant));
                let right = prefixes((0..=b).map(AffineExpression::constant));
                let joined = left.join(&right);
                assert_eq!(joined, right.join(&left));
                assert_eq!(left.join(&left), left);
                assert_eq!(
                    joined.facts[&key()]
                        .iter()
                        .map(|count| count.addend())
                        .max(),
                    Some(a.min(b))
                );
            }
        }
    }

    #[test]
    fn projection_preserves_latch_equalities_without_trusting_loop_metadata() {
        let source = VirValueId::new(1);
        let target = VirValueId::new(2);
        for value in 0..4 {
            let mut state = ResourceState::default();
            state
                .define_value(source, AbstractValue::U64(U64Interval::exact(value)))
                .unwrap();
            let remapper = ExpressionRemapper::new(&state, &[(source, target)]);
            let fact = prefixes([AffineExpression::constant(value + 1)]);
            let projected = fact.project(&remapper, &state.values);
            assert!(
                projected.facts[&key()].contains(
                    &AffineExpression::identity(target)
                        .checked_add_constant(1)
                        .unwrap()
                )
            );
            let values = BTreeMap::from([(target, AbstractValue::U64(U64Interval::exact(value)))]);
            for count in &projected.facts[&key()] {
                assert!(interval(*count, &values).unwrap().lower() <= value + 1);
            }
        }
    }

    #[test]
    fn invalidation_cannot_resurrect_valid_or_initialized_bytes() {
        for kind in 0..4 {
            let mut allocation = AbstractAllocation::new_local(40, 8).unwrap();
            allocation.initialization_prefixes = prefixes([AffineExpression::constant(4)]);
            allocation.reduce_initialization_prefixes(&BTreeMap::new());
            let range = ByteRange::new(16, 24).unwrap();
            match kind {
                0 => allocation.mark_uninitialized(range).unwrap(),
                1 => allocation.forget_initialization(range).unwrap(),
                2 => allocation.forget_validity(range).unwrap(),
                _ => allocation.forget_uninitialized(range).unwrap(),
            }
            assert_eq!(
                allocation.initialization_prefixes.facts[&key()],
                empty_prefix()
            );
            let before = allocation.clone();
            allocation.reduce_initialization_prefixes(&BTreeMap::new());
            assert_eq!(allocation, before);
        }
        let mut facts = prefixes([AffineExpression::constant(4)]);
        facts.invalidate(ByteRange::new(0, 8).unwrap());
        assert!(facts.facts[&key()].contains(&AffineExpression::constant(4)));
    }

    #[test]
    fn overflow_and_alias_budget_only_lose_precision() {
        let root = VirValueId::new(1);
        let count = AffineExpression::identity(root)
            .checked_add_constant(1)
            .unwrap();
        let values = BTreeMap::from([(root, AbstractValue::U64(U64Interval::exact(u64::MAX)))]);
        assert!(interval(count, &values).is_none());
        let mut counts = (0..=MAX_EQUIVALENT_COUNTS as u64)
            .map(AffineExpression::constant)
            .collect();
        limit_counts(&mut counts);
        assert_eq!(counts, empty_prefix());
    }

    #[test]
    fn prefix_key_budget_does_not_initialize_untracked_arrays() {
        let length = MAX_PREFIXES + 1;
        let output = crate::analyze(&crate::SourceFile::from_text(
            "prefix-budget.nera",
            format!("fn main() -> u64 {{ let mut arrays: [[u64; 1]; {length}]; return 0; }}"),
        ));
        let unit = output.vir().unwrap().as_unit();
        let access = unit.runtime.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .find_map(|i| match i.instruction {
                crate::VirInstruction::StorageReset { access, .. } => Some(access),
                _ => None,
            })
            .unwrap();
        let shape = unit.memory.object_shape(access).unwrap();
        let mut allocation =
            AbstractAllocation::new_local(shape.size_bytes(), shape.alignment()).unwrap();
        allocation.seed_initialization_prefixes(&unit.memory, &shape);
        assert_eq!(allocation.initialization_prefixes.facts.len(), MAX_PREFIXES);
        for counts in allocation.initialization_prefixes.facts.values_mut() {
            *counts = BTreeSet::from([AffineExpression::constant(1)]);
        }
        allocation.reduce_initialization_prefixes(&BTreeMap::new());
        assert_eq!(
            allocation
                .initialization()
                .classify(ByteRange::new(0, (MAX_PREFIXES * 8) as u64).unwrap()),
            InitializationClass::Initialized
        );
        let untracked = ByteRange::new((MAX_PREFIXES * 8) as u64, (length * 8) as u64).unwrap();
        assert_eq!(
            allocation.initialization().classify(untracked),
            InitializationClass::Uninitialized
        );
        assert!(!allocation.valid_value_bytes().contains(untracked));
    }
}
