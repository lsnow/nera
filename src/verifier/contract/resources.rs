//! Compiled resource observations over the canonical access rules and occurrence
//! ledger. No permission, allocation, loan or runtime value is created here.
use super::*;
use crate::verifier::{
    spec::separation::MatchLedger,
    transfer::{SpecMemoryQuery, query_spec_memory, spec_footprint},
    vc::{
        SnapshotValues, VcArena, VcLimits, VcNormalizer, VcQueryBudget, VcTermId,
        evaluate_contract_u64,
    },
};
use crate::{SpecAssertionKind as A, VirSpecSnapshot as S};

#[derive(Clone, Debug, PartialEq, Eq)]
struct Requirement {
    pointer: S,
    authority: Option<S>,
    start: VcTermId,
    end: VcTermId,
    layout: VirMemoryAccess,
    access: AccessPermission,
    initialized: bool,
    valid: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Leaf {
    Witness(VcTermId, crate::VirSpecType),
    Pure(VcTermId),
    Access(Requirement),
    Disjoint(Requirement, Requirement),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::verifier) struct ResourceContract {
    function: crate::VirFunctionId,
    memory: crate::VirMemorySchema,
    arena: VcArena,
    clauses: Vec<(ContractFactOrigin, Vec<Leaf>, bool)>,
}

enum Frame {
    Visit(crate::VirSpecAssertionId),
    Exit(u32),
}

impl ResourceContract {
    pub(super) fn new(
        unit: &ResolvedVirUnit<'_>,
        contract: &crate::VirContract,
    ) -> Result<Option<Self>, ContractDefinitionError> {
        let mut normalizer = VcNormalizer::new(VcLimits::default());
        let mut clauses = Vec::new();
        for id in &contract.clauses {
            let clause = unit.as_unit().specs.clause(*id).unwrap();
            let VirSpecClauseKind::Assertion { root } = clause.kind else {
                continue;
            };
            if matches!(
                unit.as_unit().specs.assertions()[root.get() as usize].kind,
                A::Footprint { .. }
            ) {
                continue;
            }
            let fail = || ContractDefinitionError::UnsupportedLogicalClause(*id);
            // Resource bounds/witnesses do not yet bind heap observations.
            // Reject them before normalization could erase their definedness.
            if unit.as_unit().specs.terms().iter().any(|term| {
                term.clause == *id
                    && matches!(
                        term.kind,
                        crate::VirSpecTermKind::Snapshot(S::Memory { .. })
                    )
            }) {
                return Err(fail());
            }
            let origin = ContractFactOrigin {
                clause: *id,
                position: contract_clause_position(contract.id, clause)?,
                source: clause.origin,
                source_span: unit
                    .as_unit()
                    .source_map
                    .source_span_for_origin(clause.origin.origin())
                    .ok_or_else(fail)?
                    .span,
            };
            let mut leaves = Vec::new();
            let mut pending = vec![Frame::Visit(root)];
            let mut bindings = BTreeMap::new();
            let mut existential = false;
            let mut work = 0;
            while let Some(frame) = pending.pop() {
                let id = match frame {
                    Frame::Visit(id) => id,
                    Frame::Exit(id) => {
                        bindings.remove(&id);
                        continue;
                    }
                };
                work += 1;
                if work > VcLimits::default().max_nodes {
                    return Err(fail());
                }
                let assertion = unit
                    .as_unit()
                    .specs
                    .assertions()
                    .get(id.get() as usize)
                    .ok_or_else(fail)?;
                if let A::Exists {
                    binder,
                    body,
                    witness,
                } = assertion.kind
                {
                    existential = true;
                    let witness = normalizer
                        .normalize_bound(unit, witness.ok_or_else(fail)?, &bindings)
                        .map_err(|_| fail())?;
                    let ty = unit
                        .as_unit()
                        .specs
                        .binders()
                        .get(binder.get() as usize)
                        .ok_or_else(fail)?
                        .ty;
                    leaves.push(Leaf::Witness(witness, ty));
                    if bindings.insert(binder.get(), witness).is_some() {
                        return Err(fail());
                    }
                    pending.push(Frame::Exit(binder.get()));
                    pending.push(Frame::Visit(body));
                    continue;
                }
                if let A::Pure(root) = assertion.kind {
                    leaves.push(Leaf::Pure(
                        normalizer
                            .normalize_bound(unit, root, &bindings)
                            .map_err(|_| fail())?,
                    ));
                    continue;
                }
                if let A::Disjoint { left, right } = &assertion.kind {
                    let mut range = |r: &crate::SpecMemoryRange<S, crate::VirSpecTermId, VirMemoryAccess>| -> Result<Requirement, ContractDefinitionError> {
                        Ok(Requirement { pointer: r.pointer, authority: None, start: normalizer.normalize_bound(unit, r.start_bytes, &bindings).map_err(|_| fail())?, end: normalizer.normalize_bound(unit, r.end_bytes, &bindings).map_err(|_| fail())?, layout: r.layout, access: AccessPermission::Read, initialized: false, valid: false })
                    };
                    leaves.push(Leaf::Disjoint(range(left)?, range(right)?));
                    continue;
                }
                let (pointer, authority, start, end, layout, access, initialized, valid) =
                    match &assertion.kind {
                        A::Separation(children) => {
                            pending.extend(children.iter().rev().copied().map(Frame::Visit));
                            continue;
                        }
                        A::Initialized {
                            pointer,
                            start_bytes,
                            end_bytes,
                            layout,
                        } => (
                            *pointer,
                            None,
                            *start_bytes,
                            *end_bytes,
                            *layout,
                            AccessPermission::Read,
                            true,
                            false,
                        ),
                        A::Permission(memory)
                        | A::PointsTo {
                            memory,
                            value: None,
                        } => (
                            memory.pointer,
                            Some(memory.authority),
                            memory.start_bytes,
                            memory.end_bytes,
                            memory.layout,
                            match memory.access {
                                crate::SpecAccess::Read => AccessPermission::Read,
                                crate::SpecAccess::Write => AccessPermission::Write,
                            },
                            matches!(assertion.kind, A::PointsTo { .. }),
                            matches!(assertion.kind, A::PointsTo { .. }),
                        ),
                        // Heap-valued points-to is not silently treated as a
                        // premise. Scalar heap contracts use the memory observer.
                        _ => return Err(fail()),
                    };
                leaves.push(Leaf::Access(Requirement {
                    pointer,
                    authority,
                    start: normalizer
                        .normalize_bound(unit, start, &bindings)
                        .map_err(|_| fail())?,
                    end: normalizer
                        .normalize_bound(unit, end, &bindings)
                        .map_err(|_| fail())?,
                    layout,
                    access,
                    initialized,
                    valid,
                }));
            }
            clauses.push((origin, leaves, existential));
        }
        Ok((!clauses.is_empty()).then(|| Self {
            function: contract.function,
            memory: unit.runtime().memory.clone(),
            arena: normalizer.arena().clone(),
            clauses,
        }))
    }

    pub(in crate::verifier) fn check(
        &self,
        state: &ResourceState,
        entry: &ResourceState,
        inputs: &[VirValueId],
        results: &[VirValueId],
        position: VirContractPosition,
        config: crate::CfgAnalysisConfig,
    ) -> Vec<ContractCheck> {
        let source = if position == VirContractPosition::Requires {
            state
        } else {
            entry
        };
        let mut snapshots = BTreeMap::new();
        for (slot, id) in inputs.iter().enumerate() {
            if let Some(value) = source.value(*id) {
                let value = (*value, source.word_expression(*id));
                snapshots.insert(
                    S::Parameter {
                        function: self.function,
                        slot: slot as u32,
                    },
                    value,
                );
                snapshots.insert(
                    S::EntryParameter {
                        function: self.function,
                        slot: slot as u32,
                    },
                    value,
                );
            }
        }
        for (slot, id) in results.iter().enumerate() {
            if let Some(value) = state.value(*id) {
                snapshots.insert(
                    S::Result {
                        function: self.function,
                        slot: slot as u32,
                    },
                    (*value, state.word_expression(*id)),
                );
            }
        }
        let values = SnapshotValues::Bound {
            state,
            snapshots: &snapshots,
        };
        let mut budget = VcQueryBudget::new(VcLimits::default());
        budget.relation_limits = config.relation_limits;
        // One ledger across ALL explicit clauses, not one fresh ledger per leaf.
        let mut ledger = MatchLedger::new(config.max_region_pairs_per_instruction);
        self.clauses
            .iter()
            .filter(|(origin, _, _)| origin.position == position)
            .map(|(origin, leaves, existential)| {
                let result = (|| {
                    for leaf in leaves {
                        budget.charge(1)?;
                        match leaf {
                            Leaf::Witness(term, ty) => {
                                match ty {
                                    crate::VirSpecType::U64 => {
                                        evaluate_contract_u64(
                                            &self.arena,
                                            *term,
                                            values,
                                            &mut budget,
                                        )?;
                                    }
                                    crate::VirSpecType::Bool => {
                                        crate::verifier::vc::evaluate_contract_bool(
                                            &self.arena,
                                            *term,
                                            values,
                                            &mut budget,
                                        )?;
                                    }
                                }
                                continue;
                            }
                            Leaf::Pure(term) => {
                                match crate::verifier::vc::evaluate_contract_bool(
                                    &self.arena,
                                    *term,
                                    values,
                                    &mut budget,
                                )? {
                                    AbstractBool::True => continue,
                                    AbstractBool::False => return Some(ObligationStatus::Refuted),
                                    AbstractBool::Unknown => return None,
                                }
                            }
                            _ => {}
                        }
                        let query_for = |leaf: &Requirement,
                                         budget: &mut VcQueryBudget|
                         -> Option<SpecMemoryQuery> {
                            let pointer = self.binding(
                                leaf.pointer,
                                state,
                                source,
                                inputs,
                                results,
                                position,
                                budget,
                            )?;
                            let authority = match leaf.authority {
                                Some(snapshot) => Some(self.binding(
                                    snapshot, state, source, inputs, results, position, budget,
                                )?),
                                None => None,
                            };
                            Some(SpecMemoryQuery {
                                pointer,
                                authority,
                                start: evaluate_contract_u64(
                                    &self.arena,
                                    leaf.start,
                                    values,
                                    budget,
                                )?,
                                end: evaluate_contract_u64(&self.arena, leaf.end, values, budget)?,
                                layout: leaf.layout,
                                access: leaf.access,
                                initialized: leaf.initialized,
                                valid: leaf.valid,
                            })
                        };
                        if let Leaf::Disjoint(left, right) = leaf {
                            let left = query_for(left, &mut budget)?;
                            let right = query_for(right, &mut budget)?;
                            let status = crate::verifier::transfer::query_spec_disjoint(
                                state,
                                &self.memory,
                                left,
                                right,
                                config,
                                &mut budget,
                            )?;
                            if !status.is_proven() {
                                return Some(status);
                            }
                            continue;
                        }
                        let Leaf::Access(leaf) = leaf else {
                            unreachable!()
                        };
                        let query = query_for(leaf, &mut budget)?;
                        let status =
                            query_spec_memory(state, &self.memory, query, config, &mut budget)?;
                        if !status.is_proven() {
                            return Some(status);
                        }
                        if query.authority.is_some() {
                            let status = ledger.reserve(
                                state,
                                spec_footprint(state, query)?,
                                &mut budget,
                            )?;
                            if !status.is_proven() {
                                return Some(status);
                            }
                        }
                    }
                    Some(ObligationStatus::Proven)
                })()
                .unwrap_or(ObligationStatus::Unknown);
                let result = if *existential && result == ObligationStatus::Refuted {
                    ObligationStatus::Unknown
                } else {
                    result
                };
                ContractCheck {
                    clause: origin.clause,
                    origin: *origin,
                    status: result,
                }
            })
            .collect()
    }

    #[allow(clippy::too_many_arguments)]
    fn binding(
        &self,
        snapshot: S,
        state: &ResourceState,
        entry: &ResourceState,
        inputs: &[VirValueId],
        results: &[VirValueId],
        position: VirContractPosition,
        budget: &mut VcQueryBudget,
    ) -> Option<VirValueId> {
        match snapshot {
            S::Parameter { function, slot } if function == self.function => {
                let id = *inputs.get(slot as usize)?;
                if position == VirContractPosition::Requires {
                    Some(id)
                } else {
                    super::pure::current_entry_binding(id, entry, state, budget)
                }
            }
            S::Result { function, slot } if function == self.function => {
                results.get(slot as usize).copied()
            }
            _ => None,
        }
    }
}
