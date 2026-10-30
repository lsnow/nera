//! Instantiated counts consume ordinary initialization evidence. The logical
//! value does not mark its numeric upper envelope as initialized.
use super::*;
type Prefix = crate::PredicateInitializedPrefix<VirMemoryAccess>;

/// A checked initialized range over an immutable logical endpoint. This is
/// storage evidence, not an authority or an interval-derived assumption.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::verifier::resource::predicate) struct LogicalInitialization {
    pub(super) allocation: AbstractAllocationId,
    pub(super) array_offset: u64,
    pub(super) element: VirMemoryAccess,
    pub(super) length: u64,
    pub(super) stride: u64,
    pub(super) revision: u64,
    pub(super) count: PredicateLogicValue,
}

impl ResourceState {
    /// Re-express a checked package's initialized-prefix clause in its new
    /// existential namespace. Only the resource boundary may call this after
    /// admitting the original package and its parameter abstraction. This is
    /// existential elimination, not a fold or a proof from numeric bounds.
    /// No runtime slots or initialized/valid byte envelopes are created.
    pub(super) fn abstract_predicate_logical_prefixes(
        &self,
        instance: &PredicateInstance,
        budget: &mut LogicBudget,
    ) -> Result<Vec<LogicalInitialization>, PredicateError> {
        let captured = CapturedPredicateLogic {
            scope: instance.logic_scope,
            parameters: instance.logical_parameters.clone(),
            witnesses: instance.logical_witnesses.clone(),
            facts: instance.logical_facts.clone(),
            local_aliases: BTreeMap::new(),
        };
        let counts = self.prefix_counts(
            &instance.definition,
            &instance.resources,
            &captured,
            budget,
            true,
        )?;
        instance
            .definition
            .logical_prefixes
            .iter()
            .zip(counts)
            .map(|(prefix, count)| {
                budget.charge(1).map_err(map_error)?;
                let allocation = instance
                    .resources
                    .get(prefix.resource as usize)
                    .ok_or(PredicateError::InvalidDefinition)?
                    .allocation;
                let storage = self
                    .allocation(allocation)
                    .ok_or(PredicateError::InvalidBinding)?;
                let extent = prefix
                    .length
                    .checked_mul(prefix.stride)
                    .and_then(|bytes| prefix.array_offset.checked_add(bytes))
                    .ok_or(PredicateError::InvalidDefinition)?;
                if storage.liveness() != LivenessState::Live || extent > storage.size_bytes() {
                    return Err(PredicateError::UnprovedRepresentation);
                }
                Ok(LogicalInitialization {
                    allocation,
                    array_offset: prefix.array_offset,
                    element: prefix.element,
                    length: prefix.length,
                    stride: prefix.stride,
                    revision: storage
                        .initialization_revision
                        .ok_or(PredicateError::UnprovedRepresentation)?,
                    count: TypedLogicValue {
                        ty: LogicType::Usize,
                        value: LogicValue::Word(count),
                    },
                })
            })
            .collect()
    }

    fn prefix_counts(
        &self,
        definition: &PredicateDefinition,
        resources: &[SealedResource],
        captured: &CapturedPredicateLogic,
        budget: &mut LogicBudget,
        imported: bool,
    ) -> Result<Vec<AffineValue<ObservationAtom>>, PredicateError> {
        if definition.logical_prefixes.is_empty() {
            return Ok(Vec::new());
        }
        let scope = captured.scope.ok_or(PredicateError::InvalidBinding)?;
        let mut captures = Vec::new();
        let mut queries = Vec::new();
        for prefix in &definition.logical_prefixes {
            let crate::PredicatePrefixCount::Logical(expression) = &prefix.count else {
                return Err(PredicateError::InvalidDefinition);
            };
            let leaves = self.capture_predicate_logic_leaves(
                definition,
                resources,
                scope,
                &captured.parameters,
                &captured.witnesses,
                expression,
                budget,
            )?;
            queries.extend(leaves.iter().map(|(_, value)| value.clone()));
            captures.push((prefix, expression, leaves));
        }
        let (facts, prepared) = self.established_constraint_facts_with_inputs(
            &captured.facts,
            &queries,
            Some(scope),
            budget,
        )?;
        let mut prepared = prepared.into_iter();
        let mut counts = Vec::new();
        for (prefix, expression, leaves) in captures {
            let leaves = leaves
                .into_iter()
                .map(|(id, value)| {
                    // An unretained memory observation can supply its bounds only
                    // to this evaluation. It never entered the shared premise set.
                    let qualified = prepared.next().ok_or(PredicateError::InvalidBinding)?;
                    Ok((id, Some(qualified.unwrap_or(value))))
                })
                .collect::<Result<Vec<_>, PredicateError>>()?;
            let value = facts
                .evaluate_word(expression, &leaves, budget)
                .map_err(map_error)?
                .ok_or(PredicateError::UnprovedRepresentation)?;
            let LogicValue::Word(word) = value.value else {
                return Err(PredicateError::InvalidDefinition);
            };
            let (mut word, _) = self
                .refine_predicate_word(&word)
                .ok_or(PredicateError::UnprovedRepresentation)?;
            if word.lower > prefix.length || (!imported && word.upper > prefix.length) {
                return Err(PredicateError::UnprovedRepresentation);
            }
            if imported {
                word.upper = word.upper.min(prefix.length);
            }
            counts.push(word);
        }
        Ok(counts)
    }

    fn ordinary_prefix_proven(
        &self,
        allocation: AbstractAllocationId,
        prefix: &Prefix,
        count: &AffineValue<ObservationAtom>,
        captured: &CapturedPredicateLogic,
        budget: &mut LogicBudget,
    ) -> Result<bool, PredicateError> {
        let scope = captured.scope.ok_or(PredicateError::InvalidBinding)?;
        let allocation_state = self
            .allocation(allocation)
            .ok_or(PredicateError::InvalidBinding)?;
        if allocation_state.liveness() != LivenessState::Live {
            return Ok(false);
        }
        if count.upper == 0 {
            return Ok(true);
        }
        let bytes = count
            .upper
            .checked_mul(prefix.stride)
            .ok_or(PredicateError::InvalidDefinition)?;
        let range = ByteRange::from_start_and_length(prefix.array_offset, bytes)
            .map_err(|_| PredicateError::InvalidDefinition)?;
        if allocation_state.initialization().classify(range) == InitializationClass::Initialized
            && allocation_state.valid_value_bytes().contains(range)
        {
            return Ok(true);
        }
        let required = count
            .scale(prefix.stride)
            .and_then(|word| word.add(&AffineValue::exact(prefix.array_offset)))
            .map_err(map_error)?;
        for partition in self.initialization_partitions(allocation, prefix.element) {
            budget.charge(1).map_err(map_error)?;
            let Some((begin, end)) = partition.initialized.bounds() else {
                continue;
            };
            // The prefix must start at the actual array base. A disjoint
            // initialized suffix cannot discharge it, even for equal counts.
            if begin.interval().upper() > prefix.array_offset {
                continue;
            }
            let end = self.prefix_expression_value(end.expression(), scope)?;
            if required.less_equal(&end) == Some(true) {
                return Ok(true);
            }
        }
        // Compare element counts before byte scaling. A hidden count may be
        // related to the real cursor without sharing its syntactic atom. Only
        // exact geometry and already established initialization are admitted.
        for expression in self.array_initialization_counts(
            allocation,
            prefix.array_offset,
            prefix.element,
            prefix.length,
            prefix.stride,
        ) {
            budget.charge(1).map_err(map_error)?;
            let end = self.prefix_expression_value(expression, scope)?;
            if self.predicate_prefix_relation(
                captured,
                crate::predicate_logic::facts::Comparison::LessEqual,
                count,
                &end,
                budget,
            )? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn logical_prefix_proven(
        &self,
        allocation: AbstractAllocationId,
        prefix: &Prefix,
        count: &AffineValue<ObservationAtom>,
        captured: &CapturedPredicateLogic,
        budget: &mut LogicBudget,
        retained: &[LogicalInitialization],
    ) -> Result<bool, PredicateError> {
        if self.ordinary_prefix_proven(allocation, prefix, count, captured, budget)? {
            return Ok(true);
        }
        let allocation_state = self
            .allocation(allocation)
            .ok_or(PredicateError::InvalidBinding)?;
        if allocation_state.liveness() != LivenessState::Live {
            return Ok(false);
        }
        for fact in retained.iter().chain(
            self.predicates
                .values()
                .flat_map(|instance| &instance.logical_initialization),
        ) {
            budget.charge(1).map_err(map_error)?;
            if fact.allocation != allocation
                || fact.array_offset != prefix.array_offset
                || fact.element != prefix.element
                || fact.length != prefix.length
                || fact.stride != prefix.stride
                || Some(fact.revision) != allocation_state.initialization_revision
            {
                continue;
            }
            let LogicValue::Word(end) = &fact.count.value else {
                return Err(PredicateError::InvalidBinding);
            };
            if self.predicate_prefix_relation(
                captured,
                crate::predicate_logic::facts::Comparison::LessEqual,
                count,
                end,
                budget,
            )? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(in crate::verifier::resource::predicate) fn establish_predicate_logical_prefixes(
        &mut self,
        definition: &PredicateDefinition,
        resources: &[SealedResource],
        captured: &CapturedPredicateLogic,
        imported: bool,
        retained: &[LogicalInitialization],
    ) -> Result<Vec<LogicalInitialization>, PredicateError> {
        let mut logical = Vec::new();
        let mut budget = LogicBudget::default();
        let counts = self.prefix_counts(definition, resources, captured, &mut budget, imported)?;
        for (prefix, count) in definition.logical_prefixes.iter().zip(counts) {
            let allocation = resources
                .get(prefix.resource as usize)
                .ok_or(PredicateError::InvalidDefinition)?
                .allocation;
            // Existing initialized storage is valid evidence at either side
            // of a call. Do not demand an SSA count merely to restate it.
            if self.ordinary_prefix_proven(allocation, prefix, &count, captured, &mut budget)? {
                continue;
            }
            let already_proven = self.logical_prefix_proven(
                allocation,
                prefix,
                &count,
                captured,
                &mut budget,
                retained,
            )?;
            if !imported && !already_proven {
                return Err(PredicateError::UnprovedRepresentation);
            }
            // A checked import supplies storage evidence even when its hidden
            // endpoint has no runtime reader. Keep the SSA path when available;
            // ordinary folds must prove the range before saving a certificate.
            let expression = if imported && !already_proven {
                match self.predicate_prefix_source(&count, captured, &mut budget) {
                    Ok(expression) => expression,
                    // A failed optional SSA search cannot invalidate a checked
                    // logical premise. Do not restart its budget or use any
                    // partial lookup result as a proof.
                    Err(PredicateError::Budget) => None,
                    Err(error) => return Err(error),
                }
            } else {
                None
            };
            let Some(expression) = expression else {
                let storage = self
                    .allocations
                    .get_mut(&allocation)
                    .ok_or(PredicateError::InvalidBinding)?;
                let revision = storage
                    .initialization_revision
                    .ok_or(PredicateError::UnprovedRepresentation)?;
                let extent = prefix
                    .length
                    .checked_mul(prefix.stride)
                    .and_then(|n| n.checked_add(prefix.array_offset))
                    .ok_or(PredicateError::InvalidDefinition)?;
                if extent > storage.size_bytes() {
                    return Err(PredicateError::InvalidBinding);
                }
                // Only the universally guaranteed lower prefix is concrete.
                // Adding a proven fact does not mutate or invalidate storage.
                if count.lower != 0 {
                    let bytes = count
                        .lower
                        .checked_mul(prefix.stride)
                        .ok_or(PredicateError::InvalidDefinition)?;
                    let range = ByteRange::from_start_and_length(prefix.array_offset, bytes)
                        .map_err(|_| PredicateError::InvalidDefinition)?;
                    storage.initialization.mark_initialized(range);
                    storage.valid_value_bytes.insert(range);
                }
                logical.push(LogicalInitialization {
                    allocation,
                    array_offset: prefix.array_offset,
                    element: prefix.element,
                    length: prefix.length,
                    stride: prefix.stride,
                    revision,
                    count: TypedLogicValue {
                        ty: LogicType::Usize,
                        value: LogicValue::Word(count),
                    },
                });
                continue;
            };
            self.refine_imported_prefix_domain(expression, &count, prefix.length, &mut budget)?;
            if !self.bind_array_initialization_prefix(
                allocation,
                prefix.array_offset,
                prefix.element,
                prefix.length,
                prefix.stride,
                expression,
            ) {
                return Err(PredicateError::Budget);
            }
        }
        self.reduce_initialization_prefixes();
        Ok(logical)
    }

    pub(super) fn predicate_logical_prefixes_valid(&self, instance: &PredicateInstance) -> bool {
        if instance.definition.logical_prefixes.is_empty() {
            return true;
        }
        let captured = CapturedPredicateLogic {
            scope: instance.logic_scope,
            parameters: instance.logical_parameters.clone(),
            witnesses: instance.logical_witnesses.clone(),
            facts: instance.logical_facts.clone(),
            local_aliases: BTreeMap::new(),
        };
        let mut budget = LogicBudget::default();
        let Ok(counts) = self.prefix_counts(
            &instance.definition,
            &instance.resources,
            &captured,
            &mut budget,
            false,
        ) else {
            return false;
        };
        instance
            .definition
            .logical_prefixes
            .iter()
            .zip(counts)
            .all(|(prefix, count)| {
                instance
                    .resources
                    .get(prefix.resource as usize)
                    .is_some_and(|resource| {
                        self.logical_prefix_proven(
                            resource.allocation,
                            prefix,
                            &count,
                            &captured,
                            &mut budget,
                            &instance.logical_initialization,
                        ) == Ok(true)
                    })
            })
    }
}
