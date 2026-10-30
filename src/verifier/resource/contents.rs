//! Bounded scalar contents, separate from initialization and authority.
//! Historical scalar origins are immutable; current SSA carriers and pointers
//! are not stored as content identities.
use super::*;

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub(super) struct ScalarContents(
    BTreeMap<(ByteRange, VirMemoryAccess), AbstractValue>,
    BTreeMap<HeapInitializationPrefix, bool>,
    pub(super) BTreeMap<(ByteRange, VirMemoryAccess), ScalarOrigin>,
    pub(super) BTreeMap<(ByteRange, VirMemoryAccess), BoolOrigin>,
);

/// Allocation-local relation, with no body SSA identity retained across calls.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct HeapInitializationPrefix {
    pub array_offset: u64,
    pub element: VirMemoryAccess,
    pub length: u64,
    pub stride: u64,
    pub count_offset: u64,
    pub count_access: VirMemoryAccess,
}
impl HeapInitializationPrefix {
    pub(crate) fn count_range(self) -> ByteRange {
        ByteRange::from_start_and_length(self.count_offset, 8).expect("validated cell")
    }
    fn extent(self) -> ByteRange {
        ByteRange::from_start_and_length(self.array_offset, self.length * self.stride)
            .expect("validated array")
    }
}

impl ScalarContents {
    pub(super) fn forget(&mut self, range: ByteRange) {
        self.2
            .retain(|(cell, _), _| cell.intersection(range).is_none());
        self.3
            .retain(|(cell, _), _| cell.intersection(range).is_none());
        self.0
            .retain(|(cell, _), _| cell.intersection(range).is_none());
        for (prefix, valid) in &mut self.1 {
            if prefix.count_range().intersection(range).is_some()
                || prefix.extent().intersection(range).is_some()
            {
                *valid = false;
            }
        }
    }
    pub(super) fn clear(&mut self) {
        self.0.clear();
        self.1.clear();
        self.2.clear();
        self.3.clear();
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
                .filter_map(|(key, value)| {
                    let joined = match (*value, *other.0.get(key)?) {
                        (AbstractValue::U64(a), AbstractValue::U64(b)) => {
                            AbstractValue::U64(a.join(b))
                        }
                        (AbstractValue::Bool(a), AbstractValue::Bool(b)) => {
                            AbstractValue::Bool(a.join(b))
                        }
                        _ => return None,
                    };
                    Some((*key, joined))
                })
                .collect(),
            self.1
                .iter()
                .filter_map(|(p, valid)| other.1.get(p).map(|other| (*p, *valid && *other)))
                .collect(),
            self.2
                .iter()
                .filter(|(key, value)| other.2.get(key) == Some(value))
                .map(|(key, value)| (*key, *value))
                .collect(),
            self.3
                .iter()
                .filter(|(key, value)| other.3.get(key) == Some(value))
                .map(|(key, value)| (*key, *value))
                .collect(),
        )
    }
}

impl AbstractAllocation {
    /// Refine a surviving stored value, without treating a branch assumption
    /// as a write (which would invalidate origins and initialization prefixes).
    /// Equality requires the complete immutable history, never just an address
    /// or coincidentally equal intervals.
    pub(super) fn narrow_stored_word_origin(
        &mut self,
        origin: ScalarOrigin,
        interval: U64Interval,
    ) {
        for (bytes, access, value) in self.scalar_contents() {
            if self.scalar_origin(bytes, access) == Some(origin)
                && let AbstractValue::U64(current) = value
                && let Some(narrowed) = current.intersection(interval)
            {
                self.scalar_contents
                    .0
                    .insert((bytes, access), AbstractValue::U64(narrowed));
            }
        }
    }

    pub(super) fn widen_scalar_contents(&mut self, left: &Self, right: &Self) {
        // Widening never follows an ascending sequence of heap intervals.
        self.scalar_contents
            .0
            .retain(|key, _| left.scalar_contents.0.get(key) == right.scalar_contents.0.get(key));
        self.scalar_contents
            .2
            .retain(|key, _| self.scalar_contents.0.contains_key(key));
        self.scalar_contents
            .3
            .retain(|key, _| self.scalar_contents.0.contains_key(key));
    }
    pub(crate) fn heap_prefixes(&self) -> Vec<(HeapInitializationPrefix, bool)> {
        self.scalar_contents
            .1
            .iter()
            .map(|(p, v)| (*p, *v))
            .collect()
    }
    pub(crate) fn certify_heap_prefix(&mut self, p: HeapInitializationPrefix) {
        if self.scalar_contents.1.len() < 32 || self.scalar_contents.1.contains_key(&p) {
            self.scalar_contents.1.insert(p, true);
        }
    }
    pub(crate) fn heap_prefix_valid(&self, p: HeapInitializationPrefix) -> bool {
        if self.liveness() != LivenessState::Live {
            return false;
        }
        let Some(AbstractValue::U64(count)) = self.scalar_content(p.count_range(), p.count_access)
        else {
            return false;
        };
        if count.upper() > p.length {
            return false;
        }
        if self.scalar_contents.1.get(&p) == Some(&true) || count.upper() == 0 {
            return true;
        }
        let Some(range) = count
            .upper()
            .checked_mul(p.stride)
            .and_then(|n| ByteRange::from_start_and_length(p.array_offset, n).ok())
        else {
            return false;
        };
        self.initialization().classify(range) == InitializationClass::Initialized
            && self.valid_value_bytes().contains(range)
    }
    /// Bounded, typed scalar observations only; origins are queried separately.
    pub(in crate::verifier) fn scalar_contents(
        &self,
    ) -> Vec<(ByteRange, VirMemoryAccess, AbstractValue)> {
        self.scalar_contents
            .0
            .iter()
            .filter_map(|((range, access), value)| {
                (self.scalar_content(*range, *access) == Some(*value))
                    .then_some((*range, *access, *value))
            })
            .collect()
    }
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
                if let Some(origin) = source.scalar_origin(*range, *access) {
                    self.set_scalar_origin(target, *access, origin);
                }
                if let Some(origin) = source.bool_origin(*range, *access) {
                    self.set_bool_origin(target, *access, origin);
                }
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
            Some(AbstractValue::U64(U64Interval::new(7, 42).unwrap()))
        );
        let mut widened = a.join(id, &b).unwrap();
        widened.widen_scalar_contents(&a, &b);
        assert_eq!(widened.scalar_content(cell(0), access), None);
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
    fn prefix_allocation() -> (AbstractAllocation, HeapInitializationPrefix) {
        let access = VirMemoryAccess::core_u64();
        let mut a = AbstractAllocation::new_local(72, 8).unwrap();
        a.mark_initialized(cell(0)).unwrap();
        a.mark_valid(cell(0)).unwrap();
        a.record_scalar_content(
            cell(0),
            access,
            AbstractValue::U64(U64Interval::new(0, 8).unwrap()),
        );
        let p = HeapInitializationPrefix {
            array_offset: 8,
            element: access,
            length: 8,
            stride: 8,
            count_offset: 0,
            count_access: access,
        };
        a.certify_heap_prefix(p);
        (a, p)
    }
    #[test]
    fn heap_prefix_writes_and_epochs_cannot_reuse_a_stale_witness() {
        let (a, p) = prefix_allocation();
        assert!(a.heap_prefix_valid(p));
        for range in [cell(0), cell(8), cell(64)] {
            for mutate in [
                AbstractAllocation::mark_uninitialized,
                AbstractAllocation::forget_initialization,
                AbstractAllocation::forget_validity,
                AbstractAllocation::mark_initialized,
            ] {
                let mut changed = a.clone();
                mutate(&mut changed, range).unwrap();
                assert!(!changed.heap_prefix_valid(p));
            }
        }
        let mut changed = a.clone();
        changed.record_scalar_content(cell(0), p.count_access, word(2));
        assert!(!changed.heap_prefix_valid(p));
        changed.mark_dead();
        changed.set_liveness(LivenessState::Live);
        assert!(!changed.heap_prefix_valid(p));
    }
    #[test]
    fn heap_prefix_join_requires_both_paths_and_does_not_copy_identity() {
        let (a, p) = prefix_allocation();
        let id = AbstractAllocationId::new(0);
        assert!(a.join(id, &a).unwrap().heap_prefix_valid(p));
        let mut b = a.clone();
        b.forget_validity(cell(8)).unwrap();
        assert!(!a.join(id, &b).unwrap().heap_prefix_valid(p));
        let mut other = AbstractAllocation::new_local(72, 8).unwrap();
        other.mark_initialized(cell(0)).unwrap();
        other.mark_valid(cell(0)).unwrap();
        other.copy_scalar_contents(&a, cell(0), 0);
        assert!(!other.heap_prefix_valid(p));
    }
}
