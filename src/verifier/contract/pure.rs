//! Pure contracts observe scalar SSA and bounded cell values, never creating authority.
//! Entry import is restricted to conjunctive scalar bounds and comparisons.
use super::*;
use crate::verifier::vc::{
    SnapshotValues, VcArena, VcLimits, VcNormalizer, VcQueryBudget, VcTermId,
    evaluate_contract_bool,
};
use crate::{
    VirContract, VirFunctionId, VirSpecSnapshot as S, VirSpecTermId, VirSpecTermKind as T,
};
use std::collections::BTreeSet;
mod boolean_inputs;
mod entry;
use entry::{EntryComparison, import_entry_facts};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::verifier) struct PureContract {
    contract: VirContractId,
    function: VirFunctionId,
    entry: bool,
    scratch_start: Option<u32>,
    arena: VcArena,
    clauses: Vec<(VcTermId, ContractFactOrigin)>,
    bounds: BTreeMap<S, AbstractValue>,
    entry_comparisons: Vec<EntryComparison>,
    memory: crate::VirMemorySchema,
    observations: Vec<MemoryObservation>,
    memory_uses: BTreeMap<VirSpecClauseId, BTreeSet<S>>,
    /// Unconditional SSA aliases only; equal abstract intervals do not imply
    /// the same historical input value.
    entry_aliases: BTreeMap<usize, Vec<VirValueId>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MemoryObservation {
    snapshot: S,
    pointer: u32,
    authority: u32,
    access: VirMemoryAccess,
    source: VirMemoryAccess,
    offset: u64,
    /// Physical entry scalar slot or constant element index.
    index: Option<crate::SpecMemoryIndex>,
    length: Option<crate::SpecMemoryIndex>,
}

impl PureContract {
    pub(in crate::verifier) fn observes_memory(&self) -> bool {
        !self.observations.is_empty()
    }
    pub(super) fn new(
        unit: &ResolvedVirUnit<'_>,
        contract: &VirContract,
    ) -> Result<Option<Self>, ContractDefinitionError> {
        let mut normalizer = VcNormalizer::new(VcLimits::default());
        let mut clauses = Vec::new();
        let mut bounds = BTreeMap::new();
        let mut entry_comparisons = Vec::new();
        let mut observations = Vec::new();
        let mut memory_uses: BTreeMap<VirSpecClauseId, BTreeSet<S>> = BTreeMap::new();
        for id in &contract.clauses {
            let clause = unit.as_unit().specs.clause(*id).unwrap();
            let VirSpecClauseKind::Logic { root } = clause.kind else {
                continue;
            };
            let fail = || ContractDefinitionError::UnsupportedLogicalClause(*id);
            let position = contract_clause_position(contract.id, clause)?;
            for term in unit
                .as_unit()
                .specs
                .terms()
                .iter()
                .filter(|t| t.clause == *id)
            {
                if let T::Snapshot(
                    snapshot @ S::Memory {
                        parameter,
                        projection,
                        ..
                    },
                ) = term.kind
                {
                    memory_uses.entry(*id).or_default().insert(snapshot);
                    let abi = &unit
                        .runtime()
                        .abis
                        .function(contract.function)
                        .ok_or_else(fail)?
                        .signature;
                    let binding = if let Some(i) = parameter {
                        abi.parameters().get(i as usize)
                    } else {
                        abi.results().first()
                    }
                    .ok_or_else(fail)?;
                    let slots = if parameter.is_some() {
                        binding.parameter_slots()
                    } else {
                        binding.result_slots()
                    };
                    use crate::{SpecMemoryIndex as I, SpecMemoryProjection as P};
                    let (source, length) = match (binding.value(), slots) {
                        (crate::VirAbiValue::Pointer { pointee, .. }, [_, _]) => (*pointee, None),
                        (crate::VirAbiValue::Slice { element, .. }, [_, length, _])
                            if parameter.is_some() =>
                        {
                            (*element, Some(I::Parameter(*length)))
                        }
                        _ => return Err(fail()),
                    };
                    let memory = unit.runtime().memory;
                    let (access, offset, index, length) = match projection {
                        P::Cell => (source, 0, None, None),
                        P::Field(field) => {
                            let definition = memory.field(field).ok_or_else(fail)?;
                            let offset = memory
                                .layout(source.layout)
                                .and_then(|l| l.fields.iter().find(|f| f.field == field))
                                .ok_or_else(fail)?
                                .offset_bytes;
                            (
                                memory.access(definition.ty).ok_or_else(fail)?,
                                offset,
                                None,
                                None,
                            )
                        }
                        P::Fields(path) => {
                            let mut access = source;
                            let mut offset = 0u64;
                            for field in path.fields() {
                                let definition = memory
                                    .field(*field)
                                    .filter(|f| f.owner == access.ty)
                                    .ok_or_else(fail)?;
                                let relative = memory
                                    .layout(access.layout)
                                    .and_then(|l| l.fields.iter().find(|f| f.field == *field))
                                    .ok_or_else(fail)?
                                    .offset_bytes;
                                offset = offset.checked_add(relative).ok_or_else(fail)?;
                                access = memory.access(definition.ty).ok_or_else(fail)?;
                            }
                            (access, offset, None, None)
                        }
                        P::Index(index) => {
                            let index = match index {
                                I::Constant(n) => I::Constant(n),
                                I::Parameter(i) => I::Parameter(
                                    *abi.parameters()
                                        .get(i as usize)
                                        .and_then(|b| b.parameter_slots().first())
                                        .ok_or_else(fail)?,
                                ),
                            };
                            if let Some(length) = length {
                                (source, 0, Some(index), Some(length))
                            } else {
                                let Some(crate::VirMemoryTypeKind::Array { element, length }) =
                                    memory.kind(source.ty)
                                else {
                                    return Err(fail());
                                };
                                (
                                    memory.access(*element).ok_or_else(fail)?,
                                    0,
                                    Some(index),
                                    Some(I::Constant(*length)),
                                )
                            }
                        }
                    };
                    let observation = MemoryObservation {
                        snapshot,
                        pointer: slots[0],
                        authority: *slots.last().ok_or_else(fail)?,
                        access,
                        source,
                        offset,
                        index,
                        length,
                    };
                    if !observations.contains(&observation) {
                        observations.push(observation);
                    }
                }
            }
            if position == VirContractPosition::Requires {
                import_entry_facts(unit, root, &mut bounds, &mut entry_comparisons)
                    .ok_or_else(fail)?;
            }
            clauses.push((
                normalizer.normalize(unit, root).map_err(|_| fail())?,
                ContractFactOrigin {
                    clause: *id,
                    position,
                    source: clause.origin,
                    source_span: unit
                        .as_unit()
                        .source_map
                        .source_span_for_origin(clause.origin.origin())
                        .ok_or_else(fail)?
                        .span,
                },
            ));
        }
        if clauses.is_empty() {
            return Ok(None);
        }
        Ok(Some(Self {
            contract: contract.id,
            function: contract.function,
            entry_aliases: {
                let function = unit
                    .runtime()
                    .functions
                    .iter()
                    .find(|f| f.id == contract.function)
                    .ok_or(ContractDefinitionError::UnsupportedLogicalClause(
                        contract.clauses[0],
                    ))?;
                let mut inputs: BTreeMap<usize, Vec<VirValueId>> = BTreeMap::new();
                for (id, term) in crate::verifier::summary::scalar_aliases(function) {
                    if let crate::verifier::summary::ScalarTerm::Input(slot) = term {
                        inputs.entry(slot).or_default().push(id);
                    }
                }
                inputs
            },
            entry: contract.function == unit.runtime().entry,
            scratch_start: {
                let mut max = 0;
                for function in unit.runtime().functions {
                    for block in &function.blocks {
                        for parameter in &block.parameters {
                            max = max.max(parameter.id.get());
                        }
                        for instruction in &block.instructions {
                            instruction
                                .instruction
                                .visit_results(|value| max = max.max(value.id.get()));
                        }
                    }
                }
                max.checked_add(1)
            },
            arena: normalizer.arena().clone(),
            clauses,
            bounds,
            entry_comparisons,
            memory: unit.runtime().memory.clone(),
            observations,
            memory_uses,
        }))
    }

    pub(super) fn install_entry(
        &self,
        state: &mut ResourceState,
        parameters: &[(VirValueId, VirType)],
    ) -> Result<(), ContractApplicationError> {
        // Whole-program entry has no caller that can establish a declaration.
        if self.entry {
            for (id, ty) in parameters {
                if matches!(ty, VirType::U64 | VirType::Bool) {
                    *state.value_mut(*id).expect("entry scalar") = unknown_value(*ty);
                }
            }
            return Ok(());
        }
        for (snapshot, bound) in &self.bounds {
            let S::Parameter { slot, .. } = snapshot else {
                continue;
            };
            let id = parameters[*slot as usize].0;
            let value = *state.value(id).expect("validated scalar parameter");
            // Refining a premise is not a replacement of its historical input.
            // Compute the intersection first so contradiction changes no facts.
            let narrowed = intersect(value, *bound)
                .ok_or(ContractApplicationError::SignatureMismatch(self.contract))?;
            match narrowed {
                AbstractValue::U64(interval) => state.narrow_word_interval(id, interval),
                AbstractValue::Bool(AbstractBool::True) => {
                    state.narrow_bool_value(id, true);
                }
                AbstractValue::Bool(AbstractBool::False) => {
                    state.narrow_bool_value(id, false);
                }
                AbstractValue::Bool(AbstractBool::Unknown) => {}
                _ => return Err(ContractApplicationError::SignatureMismatch(self.contract)),
            }
        }
        Ok(())
    }

    /// Prepare entry observations only after the existing ABI has installed
    /// authority. Explicit bounds refine contents; old cells without bounds
    /// receive only unknown values for history tracking. Neither operation
    /// supplies initialization, liveness, a loan, or a postcondition premise.
    pub(in crate::verifier) fn install_memory_entry(
        &self,
        state: &mut ResourceState,
        parameters: &[VirValueId],
    ) -> Option<()> {
        if self.entry {
            return Some(());
        }
        let mut budget = VcQueryBudget::new(VcLimits::default());
        let observation_state = state.predicate_observation_view();
        for observation in &self.observations {
            let declared = self.bounds.get(&observation.snapshot).copied();
            // An old cell needs an immutable entry identity even when no
            // numeric/Boolean bound was declared. Observe it only if the real
            // ABI already proves readable initialized storage. This neither
            // imports a postcondition nor makes an unreadable cell available.
            if declared.is_none()
                && !matches!(
                    observation.snapshot,
                    S::Memory {
                        parameter: Some(_),
                        old: true,
                        ..
                    }
                )
            {
                continue;
            }
            let Some(query) =
                observation.query(parameters, parameters, &observation_state, &self.memory)
            else {
                if declared.is_some() {
                    return None;
                }
                continue;
            };
            if super::super::transfer::query_contract_memory(
                &observation_state,
                &self.memory,
                query,
                observation.source,
                &mut budget,
            ) != Some(ObligationStatus::Proven)
            {
                if declared.is_some() {
                    return None;
                }
                continue;
            }
            let bound = declared.or_else(|| match self.memory.kind(observation.access.ty)? {
                crate::VirMemoryTypeKind::Bool => Some(AbstractValue::Bool(AbstractBool::Unknown)),
                crate::VirMemoryTypeKind::Integer(
                    crate::VirIntegerType::U64 | crate::VirIntegerType::Usize,
                ) => Some(AbstractValue::U64(U64Interval::unknown())),
                _ => None,
            })?;
            let AbstractValue::Pointer(pointer) = *state.value(query.pointer)? else {
                return None;
            };
            let AbstractProvenance::Known(id) = pointer.provenance() else {
                return None;
            };
            let range = ByteRange::from_start_and_length(
                pointer
                    .offset_bytes()
                    .exact_value()?
                    .checked_add(query.start)?,
                query.end.checked_sub(query.start)?,
            )
            .ok()?;
            let allocation = state.allocation_mut(id)?;
            let value = match allocation.scalar_content(range, query.layout) {
                Some(previous) => intersect(previous, bound)?,
                None => bound,
            };
            // Refining a callee premise is not a write to the cursor. Preserve
            // already established prefix relations; import no new ones.
            let prefixes = allocation
                .heap_prefixes()
                .into_iter()
                .filter_map(|(p, _)| allocation.heap_prefix_valid(p).then_some(p))
                .collect::<Vec<_>>();
            let word_origin = allocation.scalar_origin(range, query.layout);
            let bool_origin = allocation.bool_origin(range, query.layout);
            allocation.record_scalar_content(range, query.layout, value);
            if let Some(origin) = word_origin {
                allocation.set_scalar_origin(range, query.layout, origin);
            }
            if let Some(origin) = bool_origin {
                allocation.set_bool_origin(range, query.layout, origin);
            }
            for prefix in prefixes {
                allocation.certify_heap_prefix(prefix);
            }
        }
        Some(())
    }

    pub(in crate::verifier) fn check(
        &self,
        state: &ResourceState,
        entry: &ResourceState,
        inputs: &[VirValueId],
        results: &[VirValueId],
        position: VirContractPosition,
        limits: crate::verifier::relation::difference::DifferenceLimits,
    ) -> Vec<ContractCheck> {
        // Logical reads may inspect a real sealed representation, while the
        // caller's execution state retains every consumed carrier and token.
        let observed_state = state.predicate_observation_view();
        let observed_entry = entry.predicate_observation_view();
        let state = &observed_state;
        let entry = &observed_entry;
        let mut snapshots = BTreeMap::new();
        let mut booleans = boolean_inputs::BooleanInputs::default();
        let mut relation_state = state.clone();
        let mut origin_roots = BTreeMap::new();
        let mut scratch = self.scratch_start;
        let mut cell_expression = |base: crate::verifier::resource::ScalarOriginCell| {
            // Immutable scalar inputs can retain their live CFG coordinate.
            // This preserves branch relations; memory histories still require
            // separate scratch roots because their current cells may change.
            if matches!(
                base.root,
                crate::verifier::resource::ScalarOriginRoot::Parameter { .. }
            ) {
                let identity = crate::verifier::resource::ScalarOrigin {
                    first: base,
                    scale: 1,
                    second: None,
                    addend: 0,
                };
                if let Some(id) = state
                    .values()
                    .keys()
                    .find(|id| state.word_origin(**id) == Some(identity))
                {
                    return Some(
                        state
                            .word_expression(*id)
                            .unwrap_or_else(|| crate::AffineExpression::identity(*id)),
                    );
                }
            }
            let root = if let Some(root) = origin_roots.get(&base) {
                *root
            } else {
                if origin_roots.len() >= 64 {
                    return None;
                }
                let value = AbstractValue::U64(
                    U64Interval::new(base.initial_lower, base.initial_upper).ok()?,
                );
                let root = VirValueId::new(scratch?);
                scratch = scratch?.checked_add(1);
                relation_state.define_value(root, value).ok()?;
                origin_roots.insert(base, root);
                root
            };
            Some(crate::AffineExpression::identity(root))
        };
        let mut origin_expression = |origin: crate::verifier::resource::ScalarOrigin| {
            let mut expression = cell_expression(origin.first)?.checked_scale(origin.scale)?;
            if let Some((second, scale)) = origin.second {
                expression =
                    expression.checked_add(cell_expression(second)?.checked_scale(scale)?)?;
            }
            expression.checked_add_constant(origin.addend)
        };
        for (slot, id) in inputs.iter().enumerate() {
            let source = if position == VirContractPosition::Requires {
                state
            } else {
                entry
            };
            let current_alias = (position == VirContractPosition::Ensures)
                .then(|| self.entry_aliases.get(&slot))
                .flatten()
                .and_then(|aliases| {
                    aliases.iter().find(|id| {
                        matches!(
                            state.value(**id),
                            Some(AbstractValue::U64(_) | AbstractValue::Bool(_))
                        )
                    })
                });
            let (source, id) = current_alias.map_or((source, id), |id| (state, id));
            if let Some(value) = source.value(*id) {
                let expression = source
                    .word_origin(*id)
                    .and_then(&mut origin_expression)
                    .or_else(|| source.word_expression(*id))
                    .or_else(|| {
                        matches!(value, AbstractValue::U64(_))
                            .then(|| crate::AffineExpression::identity(*id))
                    });
                snapshots.insert(
                    S::Parameter {
                        function: self.function,
                        slot: slot as u32,
                    },
                    (*value, expression),
                );
                snapshots.insert(
                    S::EntryParameter {
                        function: self.function,
                        slot: slot as u32,
                    },
                    (*value, expression),
                );
                if matches!(value, AbstractValue::Bool(_)) {
                    for snapshot in [
                        S::Parameter {
                            function: self.function,
                            slot: slot as u32,
                        },
                        S::EntryParameter {
                            function: self.function,
                            slot: slot as u32,
                        },
                    ] {
                        booleans.bind(snapshot, source.bool_origin(*id));
                    }
                }
            }
        }
        for (slot, id) in results.iter().enumerate() {
            if let Some(value) = state.value(*id) {
                let expression = state
                    .word_origin(*id)
                    .and_then(&mut origin_expression)
                    .or_else(|| state.word_expression(*id))
                    .or_else(|| {
                        matches!(value, AbstractValue::U64(_))
                            .then(|| crate::AffineExpression::identity(*id))
                    });
                snapshots.insert(
                    S::Result {
                        function: self.function,
                        slot: slot as u32,
                    },
                    (*value, expression),
                );
                if matches!(value, AbstractValue::Bool(_)) {
                    booleans.bind(
                        S::Result {
                            function: self.function,
                            slot: slot as u32,
                        },
                        state.bool_origin(*id),
                    );
                }
            }
        }
        let mut budget = VcQueryBudget::new(VcLimits::default());
        budget.relation_limits = limits;
        for observation in &self.observations {
            let S::Memory { parameter, old, .. } = observation.snapshot else {
                unreachable!()
            };
            let source = if old { entry } else { state };
            let ids = if parameter.is_some() { inputs } else { results };
            let index_state = if position == VirContractPosition::Requires {
                state
            } else {
                entry
            };
            let Some(mut query) = observation.query(ids, inputs, index_state, &self.memory) else {
                continue;
            };
            // CFG argument transfer consumes the old SSA permission and binds
            // the same authority to a successor parameter. Observe that exact
            // existing authority, never a descendant loan or a widened range.
            if position == VirContractPosition::Ensures && !old && parameter.is_some() {
                let Some(pointer) =
                    current_entry_binding(query.pointer, entry, source, &mut budget)
                else {
                    continue;
                };
                let Some(authority) = query
                    .authority
                    .and_then(|id| current_entry_binding(id, entry, source, &mut budget))
                else {
                    continue;
                };
                query.pointer = pointer;
                query.authority = Some(authority);
            }
            let status = super::super::transfer::query_contract_memory(
                source,
                &self.memory,
                query,
                observation.source,
                &mut budget,
            );
            if status != Some(ObligationStatus::Proven) {
                continue;
            }
            if let Some(values) = super::super::transfer::spec_scalar_contents(
                source,
                &self.memory,
                query,
                &mut budget,
            ) && let [value] = values.as_slice()
            {
                let location = (|| {
                    let AbstractValue::Pointer(pointer) = source.value(query.pointer)? else {
                        return None;
                    };
                    let AbstractProvenance::Known(id) = pointer.provenance() else {
                        return None;
                    };
                    let bytes = ByteRange::from_start_and_length(
                        pointer
                            .offset_bytes()
                            .exact_value()?
                            .checked_add(query.start)?,
                        query.end.checked_sub(query.start)?,
                    )
                    .ok()?;
                    Some((source.allocation(id)?, bytes))
                })();
                let expression = location.and_then(|(allocation, bytes)| {
                    origin_expression(allocation.scalar_origin(bytes, query.layout)?)
                });
                if matches!(value, AbstractValue::Bool(_)) {
                    booleans.bind(
                        observation.snapshot,
                        location.and_then(|(allocation, bytes)| {
                            allocation.bool_origin(bytes, query.layout)
                        }),
                    );
                }
                snapshots.insert(observation.snapshot, (*value, expression));
            }
        }
        self.clauses
            .iter()
            .filter(|(_, origin)| origin.position == position)
            .map(|(root, origin)| {
                // Normalization may erase x == x or true || x. Memory
                // definedness remains a separate prerequisite of the clause.
                let available = self.memory_uses.get(&origin.clause).is_none_or(|uses| {
                    uses.iter().all(|snapshot| snapshots.contains_key(snapshot))
                });
                let status = match available
                    .then(|| {
                        evaluate_contract_bool(
                            &self.arena,
                            *root,
                            SnapshotValues::Bound {
                                state: &relation_state,
                                snapshots: &snapshots,
                                booleans: Some(&booleans.snapshots),
                            },
                            &mut budget,
                        )
                    })
                    .flatten()
                {
                    Some(AbstractBool::True) => ObligationStatus::Proven,
                    Some(AbstractBool::False) => ObligationStatus::Refuted,
                    _ => ObligationStatus::Unknown,
                };
                ContractCheck {
                    clause: origin.clause,
                    origin: *origin,
                    status,
                }
            })
            .collect()
    }
}

impl MemoryObservation {
    fn query(
        &self,
        ids: &[VirValueId],
        inputs: &[VirValueId],
        entry: &ResourceState,
        memory: &crate::VirMemorySchema,
    ) -> Option<super::super::transfer::SpecMemoryQuery> {
        let resolve = |index| match index {
            crate::SpecMemoryIndex::Constant(n) => Some(n),
            crate::SpecMemoryIndex::Parameter(slot) => {
                match entry.value(*inputs.get(slot as usize)?)? {
                    AbstractValue::U64(interval) => interval.exact_value(),
                    _ => None,
                }
            }
        };
        let width = memory.object_shape(self.access).ok()?.size_bytes();
        let start = if let Some(index) = self.index {
            let index = resolve(index)?;
            if index >= resolve(self.length?)? {
                return None;
            }
            self.offset.checked_add(index.checked_mul(width)?)?
        } else {
            self.offset
        };
        Some(super::super::transfer::SpecMemoryQuery {
            pointer: *ids.get(self.pointer as usize)?,
            authority: Some(*ids.get(self.authority as usize)?),
            start,
            end: start.checked_add(width)?,
            layout: self.access,
            access: AccessPermission::Read,
            initialized: true,
            valid: true,
        })
    }
}

pub(super) fn current_entry_binding(
    id: VirValueId,
    entry: &ResourceState,
    current: &ResourceState,
    budget: &mut VcQueryBudget,
) -> Option<VirValueId> {
    let expected = entry.value(id)?;
    if current.value(id) == Some(expected) {
        return Some(id);
    }
    budget.charge(current.values().len())?;
    current
        .values()
        .iter()
        .find_map(|(id, value)| (value == expected).then_some(*id))
}

fn intersect(left: AbstractValue, right: AbstractValue) -> Option<AbstractValue> {
    match (left, right) {
        (AbstractValue::U64(a), AbstractValue::U64(b)) => a.intersection(b).map(AbstractValue::U64),
        (AbstractValue::Bool(AbstractBool::Unknown), b @ AbstractValue::Bool(_)) => Some(b),
        (a @ AbstractValue::Bool(_), AbstractValue::Bool(AbstractBool::Unknown)) => Some(a),
        (a, b) if a == b => Some(a),
        _ => None,
    }
}
