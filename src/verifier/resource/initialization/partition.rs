//! A view of established facts, never an allocation or permission producer.
use super::*;

/// Allocation-relative byte ranges sharing one cursor. `remaining` means
/// remaining storage, NOT definitely uninitialized bytes or write authority.
/// Every access must still prove provenance, liveness, authority and loans.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::verifier) struct InitializationPartition {
    pub allocation: AbstractAllocationId,
    pub initialized: AbstractByteRange,
    pub remaining: AbstractByteRange,
}

impl ArrayKey {
    fn byte_bound(
        self,
        index: AffineExpression,
        values: &BTreeMap<VirValueId, AbstractValue>,
    ) -> Option<SymbolicRangeBound> {
        let expression = index
            .checked_scale(self.stride)?
            .checked_add_constant(self.base)?;
        // Unlike lower-bound reduction, a range endpoint must not saturate a
        // potentially overflowing upper bound or interpret word wrap as math.
        let bytes = expression.interval(|id| match values.get(&id)? {
            AbstractValue::U64(value) => Some(*value),
            _ => None,
        })?;
        if bytes.upper() > self.extent()?.end() || bytes.lower() < self.base {
            return None;
        }
        Some(SymbolicRangeBound::new(expression, bytes))
    }

    pub(super) fn partition(
        self,
        allocation: AbstractAllocationId,
        cursor: AffineExpression,
        values: &BTreeMap<VirValueId, AbstractValue>,
    ) -> Option<InitializationPartition> {
        let begin = self.byte_bound(self.begin, values)?;
        let cursor = self.byte_bound(cursor, values)?;
        let end = SymbolicRangeBound::constant(self.extent()?.end());
        if begin.interval().lower() > cursor.interval().upper() {
            return None;
        }
        Some(InitializationPartition {
            allocation,
            initialized: AbstractByteRange::from_bounds(begin, cursor),
            remaining: AbstractByteRange::from_bounds(cursor, end),
        })
    }
}

impl ResourceState {
    /// Only reads facts established by transfer on this path. In particular,
    /// this does not seed loop-head hypotheses or mark the remainder writable.
    pub(in crate::verifier) fn initialization_partitions(
        &self,
        id: AbstractAllocationId,
        access: VirMemoryAccess,
    ) -> Vec<InitializationPartition> {
        let Some(allocation) = self.allocation(id) else {
            return Vec::new();
        };
        if allocation.liveness() != LivenessState::Live {
            return Vec::new();
        }
        allocation
            .initialization_prefixes
            .facts
            .iter()
            .filter(|(key, _)| key.element == access)
            .flat_map(|(key, counts)| {
                counts
                    .iter()
                    .filter_map(|count| key.partition(id, *count, &self.values))
            })
            .collect()
    }
}
