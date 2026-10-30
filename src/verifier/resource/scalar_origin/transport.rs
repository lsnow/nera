//! Simultaneous renaming of actual stored histories at a resource boundary.
//! No value, initialization, authority or source relation is inferred here.
use super::*;
use crate::predicate_logic::{LogicBudget, LogicError};

#[derive(Default)]
pub(crate) struct ScalarOriginTransport {
    epoch: Option<u64>,
    words: BTreeMap<ScalarOriginCell, ScalarOriginCell>,
    booleans: BTreeMap<BoolOrigin, BoolOrigin>,
}

impl ScalarOriginTransport {
    /// Transport only a scalar explicitly copied by the call adapter. Sharing
    /// this map with allocation transport preserves actual value aliases.
    pub(crate) fn scalar(
        &mut self,
        source: &ResourceState,
        value: VirValueId,
        destination: &mut ResourceState,
        target: VirValueId,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        match source.value(value) {
            Some(AbstractValue::U64(_)) => {
                if let Some(mut origin) = source.word_origin(value) {
                    origin.first =
                        self.word(origin.first, &mut destination.next_predicate_scope, budget)?;
                    if let Some((cell, coefficient)) = origin.second {
                        origin.second = Some((
                            self.word(cell, &mut destination.next_predicate_scope, budget)?,
                            coefficient,
                        ));
                    }
                    destination.set_word_origin(target, origin);
                }
            }
            Some(AbstractValue::Bool(_)) => {
                if let Some(origin) = source.bool_origin(value) {
                    let origin =
                        self.boolean(origin, &mut destination.next_predicate_scope, budget)?;
                    destination.set_bool_origin(target, origin);
                }
            }
            _ => return Err(LogicError::InvalidNode),
        }
        Ok(())
    }

    fn fresh(&mut self, next: &mut u64) -> Result<TransportedOrigin, LogicError> {
        let epoch = if let Some(epoch) = self.epoch {
            epoch
        } else {
            let epoch = *next;
            *next = next.checked_add(1).ok_or(LogicError::Budget)?;
            self.epoch = Some(epoch);
            epoch
        };
        let index = u32::try_from(self.words.len() + self.booleans.len())
            .map_err(|_| LogicError::Budget)?;
        Ok(TransportedOrigin { epoch, index })
    }

    fn word(
        &mut self,
        cell: ScalarOriginCell,
        next: &mut u64,
        budget: &mut LogicBudget,
    ) -> Result<ScalarOriginCell, LogicError> {
        budget.charge(1)?;
        if let Some(mapped) = self.words.get(&cell) {
            return Ok(*mapped);
        }
        let mapped = ScalarOriginCell {
            root: ScalarOriginRoot::Transported(self.fresh(next)?),
            ..cell
        };
        self.words.insert(cell, mapped);
        Ok(mapped)
    }

    fn boolean(
        &mut self,
        origin: BoolOrigin,
        next: &mut u64,
        budget: &mut LogicBudget,
    ) -> Result<BoolOrigin, LogicError> {
        budget.charge(1)?;
        if let Some(mapped) = self.booleans.get(&origin) {
            return Ok(*mapped);
        }
        let mapped = BoolOrigin::Transported(self.fresh(next)?);
        self.booleans.insert(origin, mapped);
        Ok(mapped)
    }

    /// The boundary owns a candidate allocation. Only origins attached to its
    /// actual live initialized values can authorize a logical-history mapping.
    pub(crate) fn allocation(
        &mut self,
        allocation: &mut AbstractAllocation,
        next: &mut u64,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        for (bytes, access, value) in allocation.scalar_contents() {
            budget.charge(1)?;
            if allocation.liveness() != LivenessState::Live
                || allocation.initialization().classify(bytes) != InitializationClass::Initialized
                || !allocation.valid_value_bytes().contains(bytes)
            {
                allocation.scalar_contents.2.remove(&(bytes, access));
                allocation.scalar_contents.3.remove(&(bytes, access));
                continue;
            }
            match value {
                AbstractValue::U64(_) => {
                    if let Some(mut origin) = allocation.scalar_origin(bytes, access) {
                        origin.first = self.word(origin.first, next, budget)?;
                        if let Some((cell, coefficient)) = origin.second {
                            origin.second = Some((self.word(cell, next, budget)?, coefficient));
                        }
                        allocation.set_scalar_origin(bytes, access, origin);
                    }
                }
                AbstractValue::Bool(_) => {
                    if let Some(origin) = allocation.bool_origin(bytes, access) {
                        allocation.set_bool_origin(
                            bytes,
                            access,
                            self.boolean(origin, next, budget)?,
                        );
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub(crate) fn mapped_word(&self, cell: ScalarOriginCell) -> Option<ScalarOriginCell> {
        self.words.get(&cell).copied()
    }
    pub(crate) fn mapped_bool(&self, origin: BoolOrigin) -> Option<BoolOrigin> {
        self.booleans.get(&origin).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_and_memory_transport_share_only_actual_history_identities() {
        let source_id = VirValueId::new(10);
        let target_id = VirValueId::new(20);
        let bool_id = VirValueId::new(11);
        let bool_target = VirValueId::new(21);
        let mut source = ResourceState::new();
        source
            .define_value(
                source_id,
                AbstractValue::U64(U64Interval::new(1, 3).unwrap()),
            )
            .unwrap();
        source
            .define_value(bool_id, AbstractValue::Bool(AbstractBool::Unknown))
            .unwrap();
        source.seed_parameter_origins(crate::VirFunctionId::new(3), &[source_id, bool_id]);
        let cell = ByteRange::new(0, 8).unwrap();
        let mut allocation = AbstractAllocation::new_local(8, 8).unwrap();
        allocation.mark_initialized(cell).unwrap();
        allocation.mark_valid(cell).unwrap();
        allocation.record_scalar_content(
            cell,
            VirMemoryAccess::core_u64(),
            *source.value(source_id).unwrap(),
        );
        allocation.set_scalar_origin(
            cell,
            VirMemoryAccess::core_u64(),
            source.word_origin(source_id).unwrap(),
        );
        for memory_first in [false, true] {
            let mut destination = ResourceState::new();
            destination
                .define_value(target_id, *source.value(source_id).unwrap())
                .unwrap();
            destination
                .define_value(bool_target, *source.value(bool_id).unwrap())
                .unwrap();
            let mut allocation = allocation.clone();
            let mut transport = ScalarOriginTransport::default();
            let mut budget = LogicBudget::default();
            if memory_first {
                transport
                    .allocation(
                        &mut allocation,
                        &mut destination.next_predicate_scope,
                        &mut budget,
                    )
                    .unwrap();
            }
            transport
                .scalar(&source, source_id, &mut destination, target_id, &mut budget)
                .unwrap();
            transport
                .scalar(&source, bool_id, &mut destination, bool_target, &mut budget)
                .unwrap();
            if !memory_first {
                transport
                    .allocation(
                        &mut allocation,
                        &mut destination.next_predicate_scope,
                        &mut budget,
                    )
                    .unwrap();
            }
            assert_eq!(
                allocation.scalar_origin(cell, VirMemoryAccess::core_u64()),
                destination.word_origin(target_id)
            );
            assert_ne!(
                destination.word_origin(target_id),
                source.word_origin(source_id)
            );
            assert_ne!(
                destination.bool_origin(bool_target),
                source.bool_origin(bool_id)
            );
        }
    }

    #[test]
    fn transport_preserves_affine_aliases_across_the_whole_group() {
        let access = VirMemoryAccess::core_u64();
        let cell = |start| ByteRange::new(start, start + 8).unwrap();
        let root = |value| ScalarOriginCell {
            root: ScalarOriginRoot::Parameter {
                function: crate::VirFunctionId::new(1),
                value: VirValueId::new(value),
            },
            initial_lower: 1,
            initial_upper: 3,
        };
        let a = ScalarOrigin {
            first: root(90),
            scale: 1,
            second: None,
            addend: 0,
        };
        let b = ScalarOrigin {
            first: root(91),
            ..a
        };
        let sum = a.scale(2).unwrap().sum(b).unwrap().add(1).unwrap();
        let mut allocation = AbstractAllocation::new_local(24, 8).unwrap();
        allocation
            .mark_initialized(ByteRange::new(0, 24).unwrap())
            .unwrap();
        allocation
            .mark_valid(ByteRange::new(0, 24).unwrap())
            .unwrap();
        for (range, origin) in [(cell(0), sum), (cell(8), a), (cell(16), b)] {
            allocation.record_scalar_content(
                range,
                access,
                AbstractValue::U64(origin.initial_interval().unwrap()),
            );
            allocation.set_scalar_origin(range, access, origin);
        }
        let before = allocation.clone();
        let mut another = allocation.clone();
        let mut next = 5;
        let mut transport = ScalarOriginTransport::default();
        let mut budget = LogicBudget::default();
        transport
            .allocation(&mut allocation, &mut next, &mut budget)
            .unwrap();
        transport
            .allocation(&mut another, &mut next, &mut budget)
            .unwrap();
        let first = allocation.scalar_origin(cell(8), access).unwrap();
        let second = allocation.scalar_origin(cell(16), access).unwrap();
        let mapped_sum = allocation.scalar_origin(cell(0), access).unwrap();
        assert_ne!(first.first.root, a.first.root);
        assert_ne!(first.first.root, second.first.root);
        assert_eq!(
            mapped_sum,
            first.scale(2).unwrap().sum(second).unwrap().add(1).unwrap()
        );
        assert_eq!(allocation, another);
        assert_eq!(next, 6, "one namespace per transfer group");
        assert_eq!(allocation.initialization(), before.initialization());
        assert_eq!(allocation.scalar_contents(), before.scalar_contents());
        assert!(
            transport.mapped_word(root(92)).is_none(),
            "untransferred sources are not evidence"
        );
        let mut returned = ScalarOriginTransport::default();
        returned
            .allocation(&mut allocation, &mut next, &mut budget)
            .unwrap();
        assert_ne!(allocation.scalar_origin(cell(0), access), Some(mapped_sum));
    }

    #[test]
    fn exhausted_mapping_cannot_silently_supply_an_identity() {
        let mut allocation = AbstractAllocation::new_local(8, 8).unwrap();
        let cell = ByteRange::new(0, 8).unwrap();
        allocation.mark_initialized(cell).unwrap();
        allocation.mark_valid(cell).unwrap();
        allocation.record_scalar_content(
            cell,
            VirMemoryAccess::core_u64(),
            AbstractValue::U64(U64Interval::unknown()),
        );
        allocation.seed_scalar_origins(AbstractAllocationId::new(0));
        let mut transport = ScalarOriginTransport::default();
        let before = allocation.clone();
        let mut budget = LogicBudget::default();
        budget
            .charge(crate::predicate_logic::MAX_SUBSTITUTION_NODES)
            .unwrap();
        assert_eq!(
            transport.allocation(&mut allocation, &mut 0, &mut budget),
            Err(LogicError::Budget)
        );
        assert_eq!(allocation, before);
        let mut exhausted = u64::MAX;
        assert_eq!(
            transport.allocation(&mut allocation, &mut exhausted, &mut LogicBudget::default()),
            Err(LogicError::Budget)
        );
        assert_eq!(allocation, before);
    }
}
