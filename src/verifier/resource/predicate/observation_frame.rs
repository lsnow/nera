//! Actual memory observations for checked ABI and induction packages. This adapter
//! supplies immutable leaves; it does not establish logical constraints.
use super::*;
use crate::predicate_logic::{LogicBudget, LogicNodeKind, LogicType, ObservationTime};

impl ResourceState {
    pub(super) fn seed_loop_predicate_observations(
        &mut self,
        instance: &PredicateInstance,
        epoch: u64,
        budget: &mut LogicBudget,
    ) -> Result<(), PredicateError> {
        self.seed_predicate_observations(&instance.definition, &instance.resources, epoch, budget)
    }

    // Callers must establish the actual resource representation first. Missing
    // cell identity can be introduced, but missing liveness, validity, bytes or
    // authority cannot. Scope reservation and the surrounding transaction are
    // owned by the ABI/induction adapter, never by the pure constraint service.
    pub(super) fn seed_predicate_observations(
        &mut self,
        definition: &PredicateDefinition,
        resources: &[SealedResource],
        epoch: u64,
        budget: &mut LogicBudget,
    ) -> Result<(), PredicateError> {
        let mut observations = BTreeSet::new();
        let expressions =
            definition
                .logic
                .existentials
                .iter()
                .enumerate()
                // Hidden witnesses are imported existentially, not recomputed
                // from their defaults. Only projected defaults are observed.
                .filter(|(index, _)| definition.projected_witnesses.contains(&(*index as u32)))
                .filter_map(|(_, e)| e.default.as_ref())
                .chain(&definition.logic.constraints)
                .chain(definition.logical_prefixes.iter().filter_map(
                    |prefix| match &prefix.count {
                        crate::PredicatePrefixCount::Logical(expression) => Some(expression),
                        _ => None,
                    },
                ));
        for expression in expressions {
            budget
                .charge(expression.nodes.len())
                .map_err(logic::map_error)?;
            for node in &expression.nodes {
                if let LogicNodeKind::Observe {
                    resource,
                    offset,
                    access,
                    time,
                } = node.kind
                {
                    if time != ObservationTime::Current {
                        return Err(PredicateError::InvalidDefinition);
                    }
                    observations.insert((resource, offset, access));
                }
            }
        }
        for (resource, offset, access) in observations {
            budget.charge(1).map_err(logic::map_error)?;
            let (width, unknown) = match definition
                .logic_observations
                .get(&(resource, offset, access))
            {
                Some(LogicType::Bool) => (1, AbstractValue::Bool(AbstractBool::Unknown)),
                Some(LogicType::U64 | LogicType::Usize) => {
                    (8, AbstractValue::U64(U64Interval::unknown()))
                }
                _ => return Err(PredicateError::InvalidDefinition),
            };
            let bytes = ByteRange::from_start_and_length(offset, width)
                .map_err(|_| PredicateError::InvalidDefinition)?;
            let resource = resources
                .get(resource as usize)
                .ok_or(PredicateError::InvalidBinding)?;
            if resource.permission.availability() != PermissionAvailability::Available
                || !matches!(resource.permission.range(), AbstractByteRange::Exact(range) if range.contains(bytes))
            {
                return Err(PredicateError::MissingAuthority);
            }
            let allocation = self
                .allocations
                .get_mut(&resource.allocation)
                .ok_or(PredicateError::InvalidBinding)?;
            if allocation.liveness() != LivenessState::Live
                || allocation.initialization().classify(bytes) != InitializationClass::Initialized
                || !allocation.valid_value_bytes().contains(bytes)
            {
                return Err(PredicateError::UnprovedRepresentation);
            }
            if allocation.scalar_content(bytes, access).is_none() {
                allocation.record_scalar_content(bytes, access, unknown);
            }
            if !allocation.seed_cell_snapshot(ScalarCellSnapshot {
                epoch,
                allocation: resource.allocation,
                bytes,
                access,
            }) {
                return Err(PredicateError::Budget);
            }
        }
        Ok(())
    }
}
