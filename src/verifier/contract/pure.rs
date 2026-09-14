//! Pure contracts observe scalar SSA and bounded cell values, never creating authority.
//! Entry import is deliberately restricted to conjunctions of scalar bounds.
use super::*;
use crate::verifier::vc::{
    SnapshotValues, VcArena, VcLimits, VcNormalizer, VcQueryBudget, VcTermId,
    evaluate_contract_bool,
};
use crate::{
    VirContract, VirFunctionId, VirSpecSnapshot as S, VirSpecTermId, VirSpecTermKind as T,
};
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::verifier) struct PureContract {
    contract: VirContractId,
    function: VirFunctionId,
    entry: bool,
    arena: VcArena,
    clauses: Vec<(VcTermId, ContractFactOrigin)>,
    bounds: BTreeMap<S, AbstractValue>,
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
                import_bounds(unit, root, &mut bounds).ok_or_else(fail)?;
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
            arena: normalizer.arena().clone(),
            clauses,
            bounds,
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
            let value = state.value_mut(id).expect("validated scalar parameter");
            // Type-derived entry facts must not be weakened by explicit clauses.
            *value = intersect(*value, *bound)
                .ok_or(ContractApplicationError::SignatureMismatch(self.contract))?;
        }
        Ok(())
    }

    /// Refine contents only after the existing ABI has installed authority.
    /// This imports a callee premise, never initialization, liveness or a loan.
    pub(in crate::verifier) fn install_memory_entry(
        &self,
        state: &mut ResourceState,
        parameters: &[VirValueId],
    ) -> Option<()> {
        if self.entry {
            return Some(());
        }
        let mut budget = VcQueryBudget::new(VcLimits::default());
        for observation in &self.observations {
            let Some(bound) = self.bounds.get(&observation.snapshot) else {
                continue;
            };
            let query = observation.query(parameters, parameters, state, &self.memory)?;
            if super::super::transfer::query_contract_memory(
                state,
                &self.memory,
                query,
                observation.source,
                &mut budget,
            ) != Some(ObligationStatus::Proven)
            {
                return None;
            }
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
                Some(previous) => intersect(previous, *bound)?,
                None => *bound,
            };
            allocation.record_scalar_content(range, query.layout, value);
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
        let mut snapshots = BTreeMap::new();
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
                let expression = source.word_expression(*id).or_else(|| {
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
            }
        }
        for (slot, id) in results.iter().enumerate() {
            if let Some(value) = state.value(*id) {
                let expression = state.word_expression(*id).or_else(|| {
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
                snapshots.insert(observation.snapshot, (*value, None));
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
                                state,
                                snapshots: &snapshots,
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

fn import_bounds(
    unit: &ResolvedVirUnit<'_>,
    root: VirSpecTermId,
    bounds: &mut BTreeMap<S, AbstractValue>,
) -> Option<()> {
    let term = |id: VirSpecTermId| {
        unit.as_unit()
            .specs
            .terms()
            .get(id.get() as usize)
            .map(|t| &t.kind)
    };
    let parameter = |id| match term(id)? {
        T::Snapshot(
            snapshot @ (S::Parameter { .. }
            | S::Memory {
                parameter: Some(_),
                old: false,
                ..
            }),
        ) => Some(*snapshot),
        _ => None,
    };
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        if seen.len() > VcLimits::default().max_nodes {
            return None;
        }
        let (slot, value) = match term(id)? {
            T::Bool(true) => continue,
            T::And(children) => {
                pending.extend(children);
                continue;
            }
            T::Snapshot(
                snapshot @ (S::Parameter { .. }
                | S::Memory {
                    parameter: Some(_),
                    old: false,
                    ..
                }),
            ) => (*snapshot, AbstractValue::Bool(AbstractBool::True)),
            T::Not(child) => (parameter(*child)?, AbstractValue::Bool(AbstractBool::False)),
            kind @ (T::Equal { left, right }
            | T::LessThan { left, right }
            | T::LessOrEqual { left, right }) => {
                let (slot, literal, reversed) = if let Some(slot) = parameter(*left) {
                    (slot, term(*right)?, false)
                } else {
                    (parameter(*right)?, term(*left)?, true)
                };
                let value = match literal {
                    T::U64(n) => {
                        let (low, high) = match (kind, reversed) {
                            (T::Equal { .. }, _) => (*n, *n),
                            (T::LessThan { .. }, false) => (0, n.checked_sub(1)?),
                            (T::LessThan { .. }, true) => (n.checked_add(1)?, u64::MAX),
                            (T::LessOrEqual { .. }, false) => (0, *n),
                            (T::LessOrEqual { .. }, true) => (*n, u64::MAX),
                            _ => return None,
                        };
                        AbstractValue::U64(U64Interval::new(low, high).ok()?)
                    }
                    T::Bool(b) if matches!(kind, T::Equal { .. }) => AbstractValue::Bool(if *b {
                        AbstractBool::True
                    } else {
                        AbstractBool::False
                    }),
                    _ => return None,
                };
                (slot, value)
            }
            _ => return None,
        };
        let value = if let Some(previous) = bounds.get(&slot) {
            intersect(*previous, value)?
        } else {
            value
        };
        bounds.insert(slot, value);
    }
    Some(())
}
