//! Scalar content facts are installed only after the real memory obligations.
use super::*;
use crate::verifier::resource::HeapInitializationPrefix;

impl TransferBuilder<'_> {
    /// A typed scalar write preserves existing initialization of other elements.
    /// Capture only a previously proved relation, never the declared template.
    pub(super) fn scalar_write_prefix_frame(
        &self,
        pointer: VirValueId,
        access: VirMemoryAccess,
    ) -> Vec<(AbstractAllocationId, HeapInitializationPrefix)> {
        let Ok(pointer) = pointer_fact(&self.state, pointer) else {
            return Vec::new();
        };
        let AbstractProvenance::Known(id) = pointer.provenance() else {
            return Vec::new();
        };
        let Some(allocation) = self.state.allocation(id) else {
            return Vec::new();
        };
        let Some(size) = self.memory.layout(access.layout).map(|l| l.size_bytes) else {
            return Vec::new();
        };
        let Some(range) = access_envelope(pointer.offset_bytes(), size) else {
            return Vec::new();
        };
        allocation
            .heap_prefixes()
            .into_iter()
            .filter_map(|(prefix, _)| {
                let extent = prefix
                    .length
                    .checked_mul(prefix.stride)
                    .and_then(|n| ByteRange::from_start_and_length(prefix.array_offset, n).ok())?;
                (prefix.element == access
                    && extent.contains(range)
                    && !prefix.count_range().overlaps(range)
                    && allocation.heap_prefix_valid(prefix))
                .then_some((id, prefix))
            })
            .collect()
    }

    pub(super) fn restore_scalar_write_prefix_frame(
        &mut self,
        prefixes: Vec<(AbstractAllocationId, HeapInitializationPrefix)>,
    ) {
        if !self.obligations.iter().all(|o| o.is_proven()) {
            return;
        }
        for (id, prefix) in prefixes {
            if let Some(allocation) = self.state.allocation_mut(id) {
                allocation.certify_heap_prefix(prefix);
            }
        }
    }

    fn scalar_cell(
        &self,
        pointer: VirValueId,
        access: VirMemoryAccess,
    ) -> Option<(AbstractAllocationId, ByteRange)> {
        let pointer = pointer_fact(&self.state, pointer).ok()?;
        let AbstractProvenance::Known(allocation) = pointer.provenance() else {
            return None;
        };
        let size = self.memory.object_shape(access).ok()?.size_bytes();
        let range =
            ByteRange::from_start_and_length(pointer.offset_bytes().exact_value()?, size).ok()?;
        Some((allocation, range))
    }
    pub(super) fn scalar_read(
        &self,
        pointer: VirValueId,
        access: VirMemoryAccess,
    ) -> Option<AbstractValue> {
        let (id, range) = self.scalar_cell(pointer, access)?;
        self.state.allocation(id)?.scalar_content(range, access)
    }
    pub(super) fn bind_scalar_read_prefixes(
        &mut self,
        pointer: VirValueId,
        result: VirValueId,
        access: VirMemoryAccess,
    ) {
        if !self.obligations.iter().all(|o| o.is_proven()) {
            return;
        }
        let Some((id, range)) = self.scalar_cell(pointer, access) else {
            return;
        };
        if let Some(origin) = self
            .state
            .allocation(id)
            .and_then(|a| a.scalar_origin(range, access))
        {
            self.state.set_word_origin(result, origin);
        }
        if let Some(origin) = self
            .state
            .allocation(id)
            .and_then(|a| a.bool_origin(range, access))
        {
            self.state.set_bool_origin(result, origin);
        }
        let prefixes = self
            .state
            .allocation(id)
            .map(|a| a.heap_prefixes())
            .unwrap_or_default();
        for (prefix, _) in prefixes {
            if prefix.count_range() == range
                && prefix.count_access == access
                && self
                    .state
                    .allocation(id)
                    .is_some_and(|a| a.heap_prefix_valid(prefix))
            {
                let expression = self
                    .state
                    .word_expression(result)
                    .unwrap_or(AffineExpression::identity(result));
                self.state
                    .bind_heap_initialization_prefix(id, prefix, expression);
            }
        }
    }
    pub(super) fn record_scalar_write(
        &mut self,
        pointer: VirValueId,
        value: VirValueId,
        access: VirMemoryAccess,
    ) {
        if !self.obligations.iter().all(|o| o.is_proven()) {
            return;
        }
        let expression = self.state.word_expression(value);
        let origin = self.state.word_origin(value);
        let bool_origin = self.state.bool_origin(value);
        let Some(value) = self.state.value(value).copied() else {
            return;
        };
        if let Some((id, range)) = self.scalar_cell(pointer, access)
            && let Some(allocation) = self.state.allocation_mut(id)
        {
            allocation.record_scalar_content(range, access, value);
            if let Some(origin) = origin {
                allocation.set_scalar_origin(range, access, origin);
            }
            if let Some(origin) = bool_origin {
                allocation.set_bool_origin(range, access, origin);
            }
            if let AbstractValue::U64(count) = value {
                let expression = count
                    .exact_value()
                    .map(AffineExpression::constant)
                    .or(expression);
                for (prefix, _) in allocation.heap_prefixes() {
                    if prefix.count_range() == range
                        && prefix.count_access == access
                        && count.upper() <= prefix.length
                        && (allocation.heap_prefix_valid(prefix)
                            || expression
                                .is_some_and(|e| allocation.prefix_covers_count(prefix, e)))
                    {
                        allocation.certify_heap_prefix(prefix);
                    }
                }
            }
        }
    }
    pub(super) fn forget_uncertain_scalar_write(&mut self, pointer: AbstractPointer, bytes: u64) {
        let known = match pointer.provenance() {
            AbstractProvenance::Known(id) => Some(id),
            _ => None,
        };
        // Exact/enveloped writes are invalidated by the canonical allocation
        // mutators. Unbounded or unknown-alias writes must not leave content
        // or relational initialization facts behind, even on unproved paths.
        if let Some(id) = known
            && let Some(range) = access_envelope(pointer.offset_bytes(), bytes)
            && self
                .state
                .allocation(id)
                .is_some_and(|a| range.end() <= a.size_bytes())
        {
            return;
        }
        let ids = self
            .state
            .allocations()
            .keys()
            .copied()
            .filter(|id| known.is_none_or(|known| *id == known))
            .collect::<Vec<_>>();
        for id in ids {
            let allocation = self.state.allocation_mut(id).unwrap();
            let extent = ByteRange::new(0, allocation.size_bytes()).expect("allocation extent");
            allocation
                .forget_initialization(extent)
                .expect("allocation extent");
        }
    }
}
