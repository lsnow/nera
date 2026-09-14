//! Bounded scalar contents, separate from initialization and authority.
//! No SSA identities or pointers are retained across allocation epochs.
use super::*;

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub(super) struct ScalarContents(BTreeMap<(ByteRange, VirMemoryAccess), AbstractValue>);

impl ScalarContents {
    pub(super) fn forget(&mut self, range: ByteRange) {
        self.0
            .retain(|(cell, _), _| cell.intersection(range).is_none());
    }
    pub(super) fn clear(&mut self) {
        self.0.clear();
    }
    pub(super) fn record(
        &mut self,
        range: ByteRange,
        access: VirMemoryAccess,
        value: AbstractValue,
    ) {
        self.forget(range);
        if self.0.len() < 64 && matches!(value, AbstractValue::U64(_) | AbstractValue::Bool(_)) {
            self.0.insert((range, access), value);
        }
    }
    pub(super) fn get(&self, range: ByteRange, access: VirMemoryAccess) -> Option<AbstractValue> {
        self.0.get(&(range, access)).copied()
    }
    pub(super) fn join(&self, other: &Self) -> Self {
        Self(
            self.0
                .iter()
                .filter(|(key, value)| other.0.get(key) == Some(value))
                .map(|(k, v)| (*k, *v))
                .collect(),
        )
    }
}

impl AbstractAllocation {
    pub(in crate::verifier) fn scalar_content(
        &self,
        range: ByteRange,
        access: VirMemoryAccess,
    ) -> Option<AbstractValue> {
        if self.liveness != LivenessState::Live
            || self.initialization.classify(range) != InitializationClass::Initialized
            || !self.valid_value_bytes.contains(range)
        {
            return None;
        }
        self.scalar_contents.get(range, access)
    }
    pub(in crate::verifier) fn record_scalar_content(
        &mut self,
        range: ByteRange,
        access: VirMemoryAccess,
        value: AbstractValue,
    ) {
        if self.liveness == LivenessState::Live
            && range.end() <= self.size_bytes
            && self.initialization.classify(range) == InitializationClass::Initialized
            && self.valid_value_bytes.contains(range)
        {
            self.scalar_contents.record(range, access, value);
        }
    }
    pub(in crate::verifier) fn clear_scalar_contents(&mut self) {
        self.scalar_contents.clear();
    }
    pub(in crate::verifier) fn forget_scalar_contents(&mut self, range: ByteRange) {
        self.scalar_contents.forget(range);
    }
    pub(in crate::verifier) fn copy_scalar_contents(
        &mut self,
        source: &Self,
        selected: ByteRange,
        destination: u64,
    ) {
        for ((range, access), value) in &source.scalar_contents.0 {
            if range.start() < selected.start()
                || range.end() > selected.end()
                || source.scalar_content(*range, *access).is_none()
            {
                continue;
            }
            if let Some(start) = destination.checked_add(range.start() - selected.start())
                && let Ok(target) =
                    ByteRange::from_start_and_length(start, range.end() - range.start())
            {
                self.record_scalar_content(target, *access, *value);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn cell(start: u64) -> ByteRange {
        ByteRange::from_start_and_length(start, 8).unwrap()
    }
    fn allocation() -> AbstractAllocation {
        let mut a = AbstractAllocation::new_local(1024, 8).unwrap();
        let whole = ByteRange::new(0, 1024).unwrap();
        a.mark_initialized(whole).unwrap();
        a.mark_valid(whole).unwrap();
        a
    }
    fn word(n: u64) -> AbstractValue {
        AbstractValue::U64(U64Interval::exact(n))
    }
    #[test]
    fn overlap_type_and_write_invalidation_are_byte_precise() {
        let mut a = allocation();
        let access = VirMemoryAccess::core_u64();
        a.record_scalar_content(cell(0), access, word(1));
        a.record_scalar_content(cell(8), access, word(2));
        a.forget_uninitialized(ByteRange::new(4, 8).unwrap())
            .unwrap();
        assert_eq!(a.scalar_content(cell(0), access), None);
        assert_eq!(a.scalar_content(cell(8), access), Some(word(2)));
        assert_eq!(
            a.scalar_content(ByteRange::new(8, 12).unwrap(), access),
            None
        );
        a.record_scalar_content(cell(8), access, word(3));
        assert_eq!(a.scalar_content(cell(8), access), Some(word(3)));
    }
    #[test]
    fn joins_keep_only_common_contents_and_never_revive_retired_cells() {
        let access = VirMemoryAccess::core_u64();
        let id = AbstractAllocationId::new(0);
        let mut a = allocation();
        a.record_scalar_content(cell(0), access, word(42));
        let mut b = a.clone();
        assert_eq!(
            a.join(id, &b).unwrap().scalar_content(cell(0), access),
            Some(word(42))
        );
        b.record_scalar_content(cell(0), access, word(7));
        assert_eq!(
            a.join(id, &b).unwrap().scalar_content(cell(0), access),
            None
        );
        for mutate in [
            AbstractAllocation::mark_uninitialized,
            AbstractAllocation::forget_initialization,
            AbstractAllocation::forget_validity,
            AbstractAllocation::forget_object_state,
            AbstractAllocation::mark_initialized,
        ] {
            let mut retired = a.clone();
            mutate(&mut retired, cell(0)).unwrap();
            assert_eq!(retired.scalar_content(cell(0), access), None);
        }
        let historical = a.clone();
        a.mark_dead();
        a.set_liveness(LivenessState::Live);
        assert_eq!(a.scalar_content(cell(0), access), None);
        assert_eq!(historical.scalar_content(cell(0), access), Some(word(42)));
    }
    #[test]
    fn content_budget_loss_does_not_mean_zero_or_known_value() {
        let mut a = allocation();
        let access = VirMemoryAccess::core_u64();
        for i in 0..65 {
            a.record_scalar_content(cell(i * 8), access, word(i));
        }
        assert_eq!(a.scalar_content(cell(63 * 8), access), Some(word(63)));
        assert_eq!(a.scalar_content(cell(64 * 8), access), None);
        a.record_scalar_content(cell(0), access, word(99));
        assert_eq!(a.scalar_content(cell(0), access), Some(word(99)));
    }
}
