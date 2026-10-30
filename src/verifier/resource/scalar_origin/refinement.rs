//! Resource-side reduction of an established numeric bound. The numeric
//! reasoner owns the proof; this adapter only follows actual immutable aliases.
use super::*;

impl ResourceState {
    pub(in crate::verifier::resource) fn narrow_word_history(
        &mut self,
        value: VirValueId,
        interval: U64Interval,
    ) {
        let Some(origin) = self.word_origin(value) else {
            return;
        };
        for (&alias, &history) in &self.word_origins {
            if history == origin
                && let Some(AbstractValue::U64(current)) = self.values.get_mut(&alias)
                && let Some(narrowed) = current.intersection(interval)
            {
                *current = narrowed;
            }
        }
        for allocation in self.allocations.values_mut() {
            allocation.narrow_stored_word_origin(origin, interval);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn word(lower: u64, upper: u64) -> AbstractValue {
        AbstractValue::U64(U64Interval::new(lower, upper).unwrap())
    }

    fn fixture() -> (ResourceState, AbstractAllocationId, ScalarOrigin) {
        let id = AbstractAllocationId::new(0);
        let access = VirMemoryAccess::core_u64();
        let mut allocation = AbstractAllocation::new_local(24, 8).unwrap();
        let whole = ByteRange::new(0, 24).unwrap();
        allocation.mark_initialized(whole).unwrap();
        allocation.mark_valid(whole).unwrap();
        for offset in [0, 8, 16] {
            allocation.record_scalar_content(cell(offset), access, word(0, 64));
        }
        allocation.seed_scalar_origins(id);
        let origin = allocation.scalar_origin(cell(0), access).unwrap();
        // A real copied value shares history; the third equal interval does not.
        allocation.set_scalar_origin(cell(8), access, origin);
        let mut state = ResourceState::new();
        state.define_allocation(id, allocation).unwrap();
        for value in [VirValueId::new(0), VirValueId::new(1)] {
            state.define_value(value, word(0, 64)).unwrap();
            state.set_word_origin(value, origin);
        }
        (state, id, origin)
    }

    fn cell(start: u64) -> ByteRange {
        ByteRange::new(start, start + 8).unwrap()
    }

    #[test]
    fn branch_bounds_follow_surviving_history_through_memory_and_cfg_edges() {
        let (mut state, id, origin) = fixture();
        let before = state.allocation(id).unwrap().clone();
        state.narrow_word_interval(VirValueId::new(0), U64Interval::new(0, 63).unwrap());
        assert_eq!(state.value(VirValueId::new(1)), Some(&word(0, 63)));
        let projected = state.project_cfg_edge(&[]);
        let allocation = projected.allocation(id).unwrap();
        for start in [0, 8] {
            assert_eq!(
                allocation.scalar_content(cell(start), VirMemoryAccess::core_u64()),
                Some(word(0, 63))
            );
            assert_eq!(
                allocation.scalar_origin(cell(start), VirMemoryAccess::core_u64()),
                Some(origin)
            );
        }
        assert_eq!(
            allocation.scalar_content(cell(16), VirMemoryAccess::core_u64()),
            Some(word(0, 64))
        );
        assert_eq!(allocation.initialization(), before.initialization());
        assert_eq!(allocation.valid_value_bytes(), before.valid_value_bytes());
    }

    #[test]
    fn writes_and_disagreeing_joins_do_not_reuse_bounds_from_old_values() {
        let (initial, id, origin) = fixture();
        for mutation in 0..4 {
            let mut state = initial.clone();
            let allocation = state.allocation_mut(id).unwrap();
            allocation.record_scalar_content(cell(0), VirMemoryAccess::core_u64(), word(0, 64));
            match mutation {
                0 => {} // A new equal interval is not the old value.
                1 => allocation.set_scalar_origin(
                    cell(0),
                    VirMemoryAccess::core_u64(),
                    origin.add(1).unwrap(),
                ),
                2 => allocation.forget_initialization(cell(0)).unwrap(),
                3 => {
                    let joined = allocation
                        .join(id, initial.allocation(id).unwrap())
                        .unwrap();
                    *allocation = joined;
                }
                _ => unreachable!(),
            }
            state.narrow_word_interval(VirValueId::new(0), U64Interval::new(0, 63).unwrap());
            let allocation = state.allocation(id).unwrap();
            assert_eq!(
                allocation.scalar_content(cell(0), VirMemoryAccess::core_u64()),
                if mutation == 2 {
                    None
                } else {
                    Some(word(0, 64))
                }
            );
            // Disjoint copied storage still holds the old value.
            assert_eq!(
                allocation.scalar_content(cell(8), VirMemoryAccess::core_u64()),
                Some(word(0, 63))
            );
        }
    }
}
