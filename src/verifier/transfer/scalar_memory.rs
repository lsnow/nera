//! Scalar content facts are installed only after the real memory obligations.
use super::*;

impl TransferBuilder<'_> {
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
    pub(super) fn record_scalar_write(
        &mut self,
        pointer: VirValueId,
        value: VirValueId,
        access: VirMemoryAccess,
    ) {
        if !self.obligations.iter().all(|o| o.is_proven()) {
            return;
        }
        let Some(value) = self.state.value(value).copied() else {
            return;
        };
        if let Some((id, range)) = self.scalar_cell(pointer, access)
            && let Some(allocation) = self.state.allocation_mut(id)
        {
            allocation.record_scalar_content(range, access, value);
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
