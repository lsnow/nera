use super::*;
use crate::verifier::{
    AbstractAllocationId, AbstractByteRange, AbstractPermission, AbstractPointer,
    AbstractProvenance, AbstractValue, FunctionCfgAnalysis, FunctionPostconditionCheck,
    MovePathState, PathFact, PermissionAuthority, ResourceState, SpecProof, SymbolicRangeBound,
};
use crate::{
    BorrowGuardAtom, VirAbiSignature, VirConstant, VirFieldId, VirFunction, VirInstruction,
    VirNominalPath, VirPointerDomain, VirTerminator, VirType, VirValueId, VirVariantId,
};
use std::collections::{BTreeMap, BTreeSet};

/// Project finalized must facts and the independent canonical may-event journal.
/// Event loss or an opaque call never becomes an empty write footprint.
pub(crate) fn project(
    program: &ResolvedVirUnit<'_>,
    function: &VirFunction,
    cfg: &FunctionCfgAnalysis,
    post: &[FunctionPostconditionCheck],
    proofs: &[SpecProof],
    binding: SummaryBinding,
) -> Result<FunctionSummary, SummaryValidationError> {
    let entry_block = function
        .blocks
        .iter()
        .find(|b| b.id == function.entry)
        .unwrap();
    let entry_view = if program
        .as_unit()
        .specs
        .predicate_interfaces()
        .iter()
        .any(|i| i.function == function.id && !i.ensures)
    {
        let contracts = crate::verifier::contract::instantiate_contracts(program)
            .map_err(|_| SummaryValidationError::Resource)?;
        let contract = contracts
            .get(function.contract)
            .ok_or(SummaryValidationError::Resource)?;
        std::borrow::Cow::Owned(
            contract
                .predicate_entry_abi_view(
                    cfg.function_entry_state(),
                    &entry_block
                        .parameters
                        .iter()
                        .map(|p| p.id)
                        .collect::<Vec<_>>(),
                )
                .map_err(|_| SummaryValidationError::Resource)?,
        )
    } else {
        std::borrow::Cow::Borrowed(cfg.function_entry_state())
    };
    let entry = &*entry_view;
    let abi = &program
        .runtime()
        .abis
        .function(function.id)
        .unwrap()
        .signature;
    let mut projector = Projector {
        function,
        path_parameters: abi
            .parameters()
            .iter()
            .map(|binding| binding.parameter_slots().first().map(|slot| *slot as usize))
            .collect(),
        aliases: aliases(function),
        result_aliases: BTreeMap::new(),
        result_offset_aliases: BTreeMap::new(),
        names: BTreeMap::new(),
        loans: BTreeMap::new(),
        stored_loans: BTreeMap::new(),
        losses: BTreeSet::new(),
    };
    for (index, parameter) in entry_block.parameters.iter().enumerate() {
        if let Some(value) = entry.value(parameter.id) {
            projector.discover(
                entry,
                provenance(*value),
                ResourceName::Input {
                    parameter: index,
                    payload_offsets: Vec::new(),
                },
            );
            if let AbstractValue::Permission(permission) = value
                && let PermissionAuthority::Loan(loan) = permission.authority()
            {
                projector.loans.entry(loan).or_insert(index);
            }
        }
    }
    projector.discover_stored_loans(entry, program.runtime().memory);
    let inputs = entry_block
        .parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| ValueMapping {
            coordinate: ValueReference {
                epoch: ValueEpoch::Pre,
                coordinate: ValueCoordinate::Parameter(index),
            },
            value: projector.value(
                *entry.value(parameter.id).unwrap(),
                Some(parameter.id),
                entry,
            ),
        })
        .collect();
    let input_resources = projector.resources(entry);
    let input_shape = input_resources.iter().map(|r| r.name.clone()).collect();
    let input_names = projector.names.clone();
    // World-relative effects are a bounded projection of the shared journal,
    // not an unbounded return-count × event-count expansion.
    let effects_fit = cfg
        .summary_events
        .events
        .len()
        .saturating_mul(cfg.returns().len())
        <= binding.config.max_relation_evidence;
    if !effects_fit {
        projector.losses.insert(SummaryLoss::ResourceProjection);
    }
    let mut alternatives: Vec<ReturnAlternative> = Vec::new();
    for (return_evidence, returned) in cfg.returns().iter().enumerate() {
        projector.names = input_names.clone();
        for value in returned.values() {
            let next = projector.fresh_index();
            projector.discover(
                returned.state(),
                provenance(*value),
                ResourceName::Fresh(next),
            );
        }
        // Input objects may acquire new escaping payloads during the body.
        let roots = projector.names.clone();
        for (id, name) in roots {
            projector.discover_children(returned.state(), id, &name, false);
        }
        let state = returned.state();
        let guard = projector.guard(state);
        // A conditional mutable return exports a checked child loan.  Summary
        // coordinates deliberately erase that callee-local child identity and
        // retain its interface-root input authority.
        for (&loan, fact) in state.loans() {
            let mut parent = fact.parent();
            while let Some(current) = parent {
                if let Some(index) = projector.loans.get(&current).copied() {
                    projector.loans.insert(loan, index);
                    break;
                }
                parent = state.loan(current).and_then(|loan| loan.parent());
            }
        }
        let ids = function
            .blocks
            .iter()
            .find(|b| b.id == returned.block())
            .and_then(|b| match &b.terminator.terminator {
                VirTerminator::Return { values } => Some(values),
                _ => None,
            })
            .unwrap();
        projector.result_aliases.clear();
        projector.result_offset_aliases.clear();
        if abi.borrow_result().is_some_and(|r| {
            matches!(
                r.projection,
                crate::BorrowProjection::ArraySlice {
                    start: crate::BorrowSliceBound::ReturnedOffset,
                    ..
                }
            )
        }) {
            let slot = abi.results()[0].result_slots()[0] as usize;
            projector.result_offset_aliases.insert(ids[slot], slot);
        }
        // Only the dynamic array-slice export check certifies this output coordinate.
        // Ordinary scalar/recursive summaries retain their existing abstraction.
        if abi.borrow_result().is_some_and(|r| {
            matches!(
                r.projection,
                crate::BorrowProjection::ArraySlice {
                    end: crate::BorrowSliceBound::ReturnedLength,
                    ..
                }
            )
        }) {
            let index = abi.results()[0].result_slots()[1] as usize;
            let id = ids[index];
            if matches!(returned.values()[index], AbstractValue::U64(_)) {
                if let Some(expr) = state.word_expression(id)
                    && expr.addend() == 0
                    && let [Some((root, 1)), None] = expr.terms()
                {
                    projector.result_aliases.insert(root, index);
                }
                projector.result_aliases.insert(id, index);
            }
        }
        let normalized = crate::verifier::borrow_interface::normalize_returned_slice(
            state,
            ids,
            returned.values(),
            abi,
        );
        if normalized.is_none() {
            projector.losses.insert(SummaryLoss::ResourceProjection);
        }
        let normalized = normalized.as_deref().unwrap_or(returned.values());
        let values = normalized
            .iter()
            .zip(ids)
            .enumerate()
            .map(|(index, (value, id))| ValueMapping {
                coordinate: ValueReference {
                    epoch: ValueEpoch::Post,
                    coordinate: ValueCoordinate::Result(index),
                },
                value: projector.value(*value, Some(*id), state),
            })
            .collect::<Vec<_>>();
        // The branch guard, returned view and exported loan authority form one
        // indivisible interface world.  Checking only the union of possible
        // sources would accept a body (or corrupted artifact) that swaps the
        // true/false pointers or swaps only their permission tokens.
        if !conditional_borrow_world_matches(abi, &guard, &values, program.runtime().memory) {
            projector.losses.insert(SummaryLoss::ResourceProjection);
        }
        let resources = projector.resources(state);
        let mut borrow_restoration = Vec::new();
        for (&loan, &index) in &projector.loans.clone() {
            if let Some(current) = state.loan(loan)
                && current.parent().is_none()
                && let Some(permission) = returned.values().iter().find_map(|value| match value {
                    AbstractValue::Permission(permission)
                        if permission.authority() == PermissionAuthority::Loan(loan) =>
                    {
                        Some(*permission)
                    }
                    _ => None,
                })
            {
                borrow_restoration.push(BorrowRestoration {
                    input_permission: index,
                    activity: current.activity(),
                    permission: projector.permission(permission),
                });
            }
        }
        // These checks are tied to the exact return evidence, not inferred
        // merely from a live payload found somewhere in the post-state.
        if returned
            .field_exports()
            .iter()
            .any(|(id, status)| !status.is_proven() || !projector.stored_loans.contains_key(id))
        {
            projector.losses.insert(SummaryLoss::ResourceProjection);
        }
        let mut stored_borrow_restoration = Vec::new();
        for (id, input) in &projector.stored_loans {
            let Some(loan) = state.loan(*id) else {
                projector.losses.insert(SummaryLoss::ResourceProjection);
                continue;
            };
            if !matches!(loan.activity(), LoanActivity::Active | LoanActivity::Ended)
                || (loan.activity() == LoanActivity::Ended && !loan.authorities().is_empty())
            {
                projector.losses.insert(SummaryLoss::ResourceProjection);
                continue;
            }
            let exit = if loan.activity() == LoanActivity::Ended {
                crate::BoundaryExit::Ended
            } else {
                let authority = SummaryAuthority::InputPayloadLoan(input.clone());
                let mut carriers = resources.iter().flat_map(|r| r.payloads.iter().filter(|&p| matches!(&p.state, SummaryMovePath::Available { permission, .. } if permission.authority == authority)).map(|p| StoredBorrowLocation { resource: r.name.clone(), offset: p.offset, access: p.access })).collect::<Vec<_>>();
                let ssa = values.iter().enumerate().filter_map(|(slot, value)|
                    matches!(&value.value, SummaryValue::Permission(p) if p.authority == authority).then_some(slot)
                ).collect::<Vec<_>>();
                carriers.sort();
                match (carriers.as_slice(), ssa.as_slice()) {
                    ([location], []) if super::borrow::is_input_location(input, location) => {
                        crate::BoundaryExit::InPlace
                    }
                    ([location], []) => crate::BoundaryExit::Stored(location.clone()),
                    ([], [slot]) => crate::BoundaryExit::Value(*slot),
                    _ if loan.kind() == crate::VirLoanKind::Shared
                        && carriers.len() + ssa.len() > 1 =>
                    {
                        crate::BoundaryExit::Shared {
                            stored: carriers,
                            values: ssa,
                        }
                    }
                    _ => {
                        projector.losses.insert(SummaryLoss::ResourceProjection);
                        continue;
                    }
                }
            };
            stored_borrow_restoration.push(StoredBorrowRestoration {
                input: input.clone(),
                exit,
            });
        }
        let world = ReturnWorld {
            effects: if effects_fit {
                projector.effects(&cfg.summary_events).0
            } else {
                SummaryEffects {
                    may_read: Knowledge::Unknown,
                    may_write: Knowledge::Unknown,
                    may_free: Knowledge::Unknown,
                }
            },
            return_evidence,
            values,
            bool_value_origins: ids
                .iter()
                .map(|id| projector.bool_origin(state.bool_origin(*id)?))
                .collect(),
            value_origins: ids
                .iter()
                .map(|id| projector.scalar_origin(state.word_origin(*id)?))
                .collect(),
            post_inputs: entry_block
                .parameters
                .iter()
                .enumerate()
                .map(|(index, parameter)| {
                    state.value(parameter.id).map(|value| ValueMapping {
                        coordinate: ValueReference {
                            epoch: ValueEpoch::Post,
                            coordinate: ValueCoordinate::Parameter(index),
                        },
                        value: projector.value(*value, Some(parameter.id), state),
                    })
                })
                .collect::<Option<Vec<_>>>()
                .map(Knowledge::Known)
                .unwrap_or(Knowledge::Unknown),
            resources,
            borrow_restoration,
            stored_borrow_restoration,
        };
        if let Some(alternative) = alternatives.iter_mut().find(|a| a.guard == guard) {
            alternative.worlds.push(world);
        } else {
            alternatives.push(ReturnAlternative {
                guard,
                worlds: vec![world],
            });
        }
    }
    // Unexportable local atoms are existentially eliminated one atom at a
    // time. Keep the remaining input guards and every complete return world;
    // neither choose a favorable return nor erase unrelated interface guards.
    let mut requirements = Vec::new();
    for (index, record) in cfg.obligations().iter().enumerate() {
        requirements.push(SummaryFinding {
            kind: EvidenceKind::Cfg,
            index,
            status: record.obligation().status(),
        });
    }
    for (index, record) in cfg.summary_pending().iter().enumerate() {
        requirements.push(SummaryFinding {
            kind: EvidenceKind::Historical,
            index,
            status: record.obligation().status(),
        });
    }
    for (index, record) in post.iter().enumerate() {
        requirements.push(SummaryFinding {
            kind: EvidenceKind::Postcondition,
            index,
            status: record.check().status,
        });
    }
    for (index, record) in proofs.iter().enumerate() {
        requirements.push(SummaryFinding {
            kind: EvidenceKind::Proof,
            index,
            status: record.status(),
        });
    }
    if requirements.iter().any(|r| !r.status.is_proven()) {
        projector.losses.insert(SummaryLoss::SafetyObligation);
    }
    // Edge projection existentially forgets local numeric SSA just as it
    // forgets local guards. All worlds and only proven must facts survive;
    // missing interface ranges still fail the separate resource projection.
    // Resource/case/solver budgets and widening remain publication barriers.
    if cfg.guarded_precision_losses().values().any(|losses| {
        losses
            .iter()
            .any(|loss| *loss != crate::verifier::GuardedStatePrecisionLoss::GuardProjection)
    }) || !cfg.widened_blocks().is_empty()
        || cfg.returns().iter().any(|r| {
            !r.state().loan_precision_losses().is_empty()
                || r.state().relations().precision_losses().iter().any(|loss| {
                    *loss != crate::verifier::relation::state::RelationPrecisionLoss::Projection
                })
        })
    {
        projector.losses.insert(SummaryLoss::AnalysisPrecision);
    }
    let (mut effects, local_effect_events) = projector.effects(&cfg.summary_events);
    // The global diagnostic footprint cannot merge world-relative Fresh(0)
    // names. Conditional call transfer uses each world's own complete effects,
    // never this lossy global view or only the last world's resource namespace.
    if alternatives.iter().map(|a| a.worlds.len()).sum::<usize>() > 1
        && alternatives.iter().flat_map(|a| &a.worlds).any(|w| {
            w.resources
                .iter()
                .any(|r| matches!(r.name, ResourceName::Fresh(_)))
        })
    {
        effects = SummaryEffects {
            may_read: Knowledge::Unknown,
            may_write: Knowledge::Unknown,
            may_free: Knowledge::Unknown,
        };
    }
    if cfg.summary_events.incomplete {
        projector.losses.insert(SummaryLoss::ResourceProjection);
    }
    // Eliminating a private guard keeps ALL complete return worlds. This loses
    // precision, not coverage, and does not invalidate the body's safety proof.
    projector.losses.remove(&SummaryLoss::GuardProjection);
    let state = if projector.losses.is_empty() {
        SummaryState::Candidate
    } else {
        SummaryState::Unknown(projector.losses.into_iter().collect())
    };
    let mut return_guards = vec![Vec::new(); cfg.returns().len()];
    for alternative in &alternatives {
        for world in &alternative.worlds {
            return_guards[world.return_evidence] = alternative.guard.clone();
        }
    }
    let summary = FunctionSummary {
        audit_complete: !cfg.summary_events.audit_overflow,
        recursion: None,
        recursion_shape: None,
        world_shapes: alternatives
            .iter()
            .flat_map(|a| a.worlds.iter().cloned())
            .collect(),
        dependency_states: dependencies(program, function, &binding)
            .iter()
            .map(|d| d.state.clone())
            .collect(),
        call_uses: cfg.summary_events.calls.clone(),
        local_effect_events,
        effects_shape: effects.clone(),
        closed: false,
        projected_state: state.clone(),
        return_guards,
        version: SUMMARY_SCHEMA_VERSION,
        verifier_profile: SUMMARY_VERIFIER_PROFILE.into(),
        dependencies: dependencies(program, function, &binding),
        binding,
        state,
        parameters: function.signature.parameters.clone(),
        results: function.signature.results.clone(),
        inputs,
        input_resources,
        input_shape,
        effects,
        normal_returns: Knowledge::Known(alternatives),
        evidence_shape: requirements.clone(),
        faults: SummaryFaults {
            requirements,
            runtime_faults: Knowledge::Unknown,
        },
        return_count: cfg.returns().len(),
    };
    summary.validate_structure(program, function.id, summary.binding.config)?;
    Ok(summary)
}

fn conditional_borrow_world_matches(
    abi: &VirAbiSignature,
    guard: &[SummaryGuard],
    values: &[ValueMapping],
    memory: &crate::VirMemorySchema,
) -> bool {
    if abi.borrow_result_alternatives().is_empty() {
        return true;
    }
    let matching = abi
        .borrow_result_alternatives()
        .iter()
        .filter(|alternative| {
            alternative.guard.iter().all(|atom| match atom {
                BorrowGuardAtom::Boolean {
                    parameter,
                    expected,
                } => abi
                    .parameters()
                    .get(*parameter as usize)
                    .and_then(|binding| binding.parameter_slots().first())
                    .is_some_and(|slot| {
                        guard.contains(&SummaryGuard::Boolean {
                            parameter: *slot as usize,
                            expected: *expected,
                        })
                    }),
            })
        })
        .collect::<Vec<_>>();
    let [alternative] = matching.as_slice() else {
        return false;
    };
    let relation = alternative.relation;
    let Some(source) = abi.parameters().get(relation.parameter as usize) else {
        return false;
    };
    let Some(result) = abi.results().get(relation.result as usize) else {
        return false;
    };
    if relation.parameter_field.is_some() {
        let Some(parameters) = abi
            .parameters()
            .iter()
            .map(|b| b.value().access())
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        let Some(results) = abi
            .results()
            .iter()
            .map(|b| b.value().access())
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        let Some(entry) =
            crate::vir::plan_parameter_field_result(memory, &parameters, &results, relation)
        else {
            return false;
        };
        let path = ResourceName::Input {
            parameter: entry.pointer_slot as usize,
            payload_offsets: vec![entry.offset_bytes],
        };
        let [pointer, permission] = result.result_slots() else {
            return false;
        };
        return matches!(values.get(*pointer as usize).map(|m| &m.value), Some(SummaryValue::Pointer(p)) if p.resource == Knowledge::Known(path.clone()))
            && matches!(values.get(*permission as usize).map(|m| &m.value), Some(SummaryValue::Permission(p)) if p.authority == SummaryAuthority::InputPayloadLoan(path));
    }
    result
        .result_slots()
        .iter()
        .zip(source.parameter_slots())
        .all(|(output, input)| {
            let Some(mapping) = values.iter().find(|mapping| {
                mapping.coordinate
                    == ValueReference {
                        epoch: ValueEpoch::Post,
                        coordinate: ValueCoordinate::Result(*output as usize),
                    }
            }) else {
                return false;
            };
            match (abi.physical().results.get(*output as usize), &mapping.value) {
                (Some(VirType::Permission), SummaryValue::Permission(permission)) => {
                    permission.authority == SummaryAuthority::InputLoan(*input as usize)
                }
                (Some(VirType::Pointer { .. }), SummaryValue::Pointer(pointer)) => {
                    pointer.resource
                        == Knowledge::Known(ResourceName::Input {
                            parameter: *input as usize,
                            payload_offsets: Vec::new(),
                        })
                }
                _ => false,
            }
        })
}

struct Projector<'a> {
    function: &'a VirFunction,
    /// Nominal parameter anchors use logical ABI ordinals, while exported
    /// coordinates use physical VIR signature slots.
    path_parameters: Vec<Option<usize>>,
    aliases: BTreeMap<VirValueId, ScalarTerm>,
    result_aliases: BTreeMap<VirValueId, usize>,
    result_offset_aliases: BTreeMap<VirValueId, usize>,
    names: BTreeMap<AbstractAllocationId, ResourceName>,
    loans: BTreeMap<crate::VirLoanId, usize>,
    stored_loans: BTreeMap<crate::VirLoanId, ResourceName>,
    losses: BTreeSet<SummaryLoss>,
}
impl Projector<'_> {
    fn discover_stored_loans(&mut self, entry: &ResourceState, memory: &crate::VirMemorySchema) {
        for (storage, name) in &self.names {
            let ResourceName::Input {
                parameter,
                payload_offsets,
            } = name
            else {
                continue;
            };
            let Some(allocation) = entry.allocation(*storage) else {
                continue;
            };
            for (key, value) in allocation.object_state().resource_payloads() {
                let MovePathState::Available(payload) = value else {
                    continue;
                };
                let PermissionAuthority::Loan(id) = payload.permission().authority() else {
                    continue;
                };
                let mut offsets = payload_offsets.clone();
                offsets.push(key.offset_bytes());
                let path = ResourceName::Input {
                    parameter: *parameter,
                    payload_offsets: offsets,
                };
                if payload_offsets.len() >= 16
                    || super::borrow::input_payload_field(
                        memory,
                        &self.function.signature.parameters,
                        &path,
                    ) != Some(key.access())
                    || !super::borrow::stored_reference_shape(
                        memory,
                        key.access(),
                        payload.pointer().memory_access(),
                        payload.permission().access(),
                        payload.permission().free_capability(),
                    )
                    || self.loans.contains_key(&id)
                    || self.stored_loans.contains_key(&id)
                    || payload.permission().free_capability() != FreeCapability::No
                    || payload.permission().availability() != PermissionAvailability::Available
                    || entry.loan(id).is_none_or(|loan| {
                        loan.activity() != crate::verifier::LoanActivity::Active
                            || !loan.authorities().contains(
                                &crate::verifier::resource::AbstractLoanAuthority::stored(
                                    *storage, *key,
                                ),
                            )
                            || loan.provenance() != payload.permission().provenance()
                            || loan.actual_range() != payload.permission().range()
                    })
                {
                    self.losses.insert(SummaryLoss::ResourceProjection);
                    continue;
                }
                self.stored_loans.insert(id, path);
            }
        }
    }
    fn bool_origin(
        &self,
        origin: crate::verifier::resource::BoolOrigin,
    ) -> Option<SummaryScalarRoot> {
        use crate::verifier::resource::BoolOrigin;
        match origin {
            // An induction observation is not the function's entry cell.
            BoolOrigin::Snapshot(_) | BoolOrigin::Transported(_) => None,
            BoolOrigin::Parameter { function, value } => {
                if function != self.function.id {
                    return None;
                }
                let entry = self
                    .function
                    .blocks
                    .iter()
                    .find(|b| b.id == self.function.entry)?;
                Some(SummaryScalarRoot::Parameter(
                    entry
                        .parameters
                        .iter()
                        .position(|p| p.id == value && p.ty == VirType::Bool)?,
                ))
            }
            BoolOrigin::Cell {
                allocation,
                bytes,
                access,
            } => {
                let resource = self.names.get(&allocation)?.clone();
                if !matches!(resource, ResourceName::Input { .. }) {
                    return None;
                }
                Some(SummaryScalarRoot::Cell {
                    resource,
                    bytes,
                    access,
                })
            }
        }
    }
    fn scalar_origin(
        &self,
        origin: crate::verifier::resource::ScalarOrigin,
    ) -> Option<SummaryScalarOrigin> {
        let source = |cell: crate::verifier::resource::ScalarOriginCell, scale| {
            use crate::verifier::resource::ScalarOriginRoot;
            let root = match cell.root {
                ScalarOriginRoot::Snapshot(_) | ScalarOriginRoot::Transported(_) => return None,
                ScalarOriginRoot::Cell {
                    allocation,
                    bytes,
                    access,
                } => {
                    let resource = self.names.get(&allocation)?.clone();
                    if !matches!(resource, ResourceName::Input { .. }) {
                        return None;
                    }
                    SummaryScalarRoot::Cell {
                        resource,
                        bytes,
                        access,
                    }
                }
                ScalarOriginRoot::Parameter { function, value } => {
                    if function != self.function.id {
                        return None;
                    }
                    let entry = self
                        .function
                        .blocks
                        .iter()
                        .find(|b| b.id == self.function.entry)?;
                    let slot = entry
                        .parameters
                        .iter()
                        .position(|p| p.id == value && p.ty == VirType::U64)?;
                    SummaryScalarRoot::Parameter(slot)
                }
            };
            Some(SummaryScalarSource { root, scale })
        };
        let first = source(origin.first, origin.scale)?;
        let second = match origin.second {
            Some((cell, scale)) => Some(source(cell, scale)?),
            None => None,
        };
        Some(SummaryScalarOrigin {
            root: first.root,
            scale: first.scale,
            addend: origin.addend,
            second,
        })
    }

    fn effects(&mut self, journal: &EffectJournal) -> (SummaryEffects, usize) {
        use super::effects::EffectKind;
        let (mut reads, mut writes, mut frees) = (Vec::new(), Vec::new(), Vec::new());
        let mut unknown = journal.incomplete;
        let mut local = 0;
        for event in &journal.events {
            if event.kind == EffectKind::Allocate {
                local += 1;
                continue;
            }
            let Some(pointer) = event.pointer else {
                unknown = true;
                continue;
            };
            let AbstractProvenance::Known(id) = pointer.provenance() else {
                unknown = true;
                continue;
            };
            let Some(name) = self.names.get(&id).cloned() else {
                local += 1;
                continue;
            };
            let footprint = SummaryFootprint {
                resource: name.clone(),
                range: self.range(event.range),
            };
            match event.kind {
                EffectKind::Read => {
                    if !reads.contains(&footprint) {
                        reads.push(footprint);
                    }
                }
                EffectKind::Write => {
                    if !writes.contains(&footprint) {
                        writes.push(footprint);
                    }
                }
                EffectKind::Free => {
                    if !frees.contains(&name) {
                        frees.push(name);
                    }
                }
                EffectKind::Allocate => unreachable!(),
            }
        }
        if unknown {
            (
                SummaryEffects {
                    may_read: Knowledge::Unknown,
                    may_write: Knowledge::Unknown,
                    may_free: Knowledge::Unknown,
                },
                local,
            )
        } else {
            (
                SummaryEffects {
                    may_read: Knowledge::Known(reads),
                    may_write: Knowledge::Known(writes),
                    may_free: Knowledge::Known(frees),
                },
                local,
            )
        }
    }
    fn fresh_index(&self) -> usize {
        self.names
            .values()
            .filter(|n| matches!(n, ResourceName::Fresh(_)))
            .count()
    }
    fn discover(
        &mut self,
        state: &ResourceState,
        provenance: AbstractProvenance,
        name: ResourceName,
    ) {
        let AbstractProvenance::Known(id) = provenance else {
            return;
        };
        if self.names.contains_key(&id) {
            return;
        }
        if state.allocation(id).is_none() {
            self.losses.insert(SummaryLoss::ResourceProjection);
            return;
        }
        self.names.insert(id, name.clone());
        self.discover_children(state, id, &name, true);
    }
    fn discover_children(
        &mut self,
        state: &ResourceState,
        id: AbstractAllocationId,
        name: &ResourceName,
        entry: bool,
    ) {
        let Some(allocation) = state.allocation(id) else {
            return;
        };
        for (key, path) in allocation.object_state().resource_payloads() {
            if let MovePathState::Available(payload) = path {
                let child = match name {
                    ResourceName::Input {
                        parameter,
                        payload_offsets,
                    } if entry => {
                        let mut offsets = payload_offsets.clone();
                        offsets.push(key.offset_bytes());
                        ResourceName::Input {
                            parameter: *parameter,
                            payload_offsets: offsets,
                        }
                    }
                    _ => ResourceName::Fresh(self.fresh_index()),
                };
                self.discover(state, payload.pointer().provenance(), child);
            }
        }
    }
    fn resource(&mut self, provenance: AbstractProvenance) -> Knowledge<ResourceName> {
        match provenance {
            AbstractProvenance::Known(id) => self
                .names
                .get(&id)
                .cloned()
                .map(Knowledge::Known)
                .unwrap_or_else(|| {
                    self.losses.insert(SummaryLoss::ResourceProjection);
                    Knowledge::Unknown
                }),
            AbstractProvenance::Unknown => Knowledge::Unknown,
        }
    }
    fn bound(&mut self, bound: SymbolicRangeBound) -> Option<SummaryBound> {
        let mut terms = BTreeMap::<usize, u64>::new();
        let mut result_terms = BTreeMap::<usize, u64>::new();
        let mut result_offset_terms = BTreeMap::<usize, u64>::new();
        let mut addend = bound.expression().addend();
        for (id, scale) in bound.expression().terms().into_iter().flatten() {
            if let Some(index) = self.result_offset_aliases.get(&id) {
                let total = result_offset_terms.entry(*index).or_default();
                *total = total.checked_add(scale)?;
                continue;
            }
            let Some(alias) = self.aliases.get(&id) else {
                let index = *self.result_aliases.get(&id)?;
                let total = result_terms.entry(index).or_default();
                *total = total.checked_add(scale)?;
                continue;
            };
            match alias {
                ScalarTerm::Constant(value) => {
                    addend = addend.checked_add(value.checked_mul(scale)?)?;
                }
                ScalarTerm::Input(index) => {
                    let total = terms.entry(*index).or_default();
                    *total = total.checked_add(scale)?;
                }
            }
        }
        Some(SummaryBound {
            terms: terms.into_iter().collect(),
            result_terms: result_terms.into_iter().collect(),
            result_offset_terms: result_offset_terms.into_iter().collect(),
            addend,
            interval: bound.interval(),
        })
    }
    fn range(&mut self, range: AbstractByteRange) -> SummaryRange {
        match range {
            AbstractByteRange::Exact(range) => SummaryRange::Exact(range),
            AbstractByteRange::Symbolic { start, end } => {
                match (self.bound(start), self.bound(end)) {
                    (Some(start), Some(end)) => SummaryRange::Symbolic { start, end },
                    _ => {
                        self.losses.insert(SummaryLoss::ResourceProjection);
                        SummaryRange::Unknown
                    }
                }
            }
            AbstractByteRange::Unknown => SummaryRange::Unknown,
        }
    }
    fn path(&mut self, path: Option<VirNominalPath>) -> Option<SummaryPath> {
        let path = path?;
        let Some((access, parameter, steps)) = path.interface_parts(self.function.id) else {
            self.losses.insert(SummaryLoss::ResourceProjection);
            return None;
        };
        let steps = steps
            .iter()
            .map(|encoded| match encoded % 4 {
                0 => VirObjectPathSegment::Field(VirFieldId::new(encoded / 4)),
                1 => VirObjectPathSegment::Variant(VirVariantId::new(encoded / 4)),
                2 => VirObjectPathSegment::TupleElement(u64::from(encoded / 4)),
                _ => VirObjectPathSegment::ArrayElement(0),
            })
            .collect();
        let parameter = match parameter {
            Some((index, role)) => {
                let Some(Some(slot)) = self.path_parameters.get(index as usize) else {
                    self.losses.insert(SummaryLoss::ResourceProjection);
                    return None;
                };
                Some((*slot, role))
            }
            None => None,
        };
        Some(SummaryPath {
            access,
            parameter,
            steps,
        })
    }
    fn pointer(&mut self, pointer: AbstractPointer) -> SummaryPointer {
        SummaryPointer {
            resource: self.resource(pointer.provenance()),
            access: pointer.memory_access(),
            offset: pointer.offset_bytes(),
            offset_expression: pointer.offset_expression().and_then(|expression| {
                self.bound(SymbolicRangeBound::new(expression, pointer.offset_bytes()))
            }),
            alignment: pointer.alignment().bytes(),
            domain: match pointer.domain() {
                VirPointerDomain::Allocation => SummaryDomain::Allocation,
                VirPointerDomain::Restricted(range) => SummaryDomain::Restricted(self.range(range)),
                VirPointerDomain::Unknown => SummaryDomain::Unknown,
            },
            object_path: self.path(pointer.paths().object),
            domain_path: self.path(pointer.paths().domain),
            slice_range: pointer.slice_footprint().map(|f| self.range(f.range)),
        }
    }
    fn permission(&mut self, permission: AbstractPermission) -> SummaryPermission {
        SummaryPermission {
            resource: self.resource(permission.provenance()),
            range: self.range(permission.range()),
            access: permission.access(),
            free: permission.free_capability(),
            availability: permission.availability(),
            authority: match permission.authority() {
                PermissionAuthority::Owner => SummaryAuthority::Owner,
                PermissionAuthority::Loan(id) => self
                    .loans
                    .get(&id)
                    .copied()
                    .map(SummaryAuthority::InputLoan)
                    .or_else(|| {
                        self.stored_loans
                            .get(&id)
                            .cloned()
                            .map(SummaryAuthority::InputPayloadLoan)
                    })
                    .unwrap_or_else(|| {
                        self.losses.insert(SummaryLoss::ResourceProjection);
                        SummaryAuthority::Unknown
                    }),
                PermissionAuthority::Unknown => SummaryAuthority::Unknown,
            },
        }
    }
    fn value(
        &mut self,
        value: AbstractValue,
        id: Option<VirValueId>,
        state: &ResourceState,
    ) -> SummaryValue {
        match value {
            AbstractValue::U64(interval) => SummaryValue::Word {
                interval,
                expression: id
                    .and_then(|id| state.word_expression(id))
                    .and_then(|expr| self.bound(SymbolicRangeBound::new(expr, interval))),
            },
            AbstractValue::EnumDiscriminant(fact) => SummaryValue::Word {
                interval: fact.interval(),
                expression: None,
            },
            AbstractValue::Bool(value) => SummaryValue::Bool(value),
            AbstractValue::Pointer(pointer) => {
                SummaryValue::Pointer(Box::new(self.pointer(pointer)))
            }
            AbstractValue::Permission(permission) => {
                SummaryValue::Permission(Box::new(self.permission(permission)))
            }
        }
    }
    fn resources(&mut self, state: &ResourceState) -> Vec<ResourcePostState> {
        let mut resources = Vec::new();
        for (id, name) in self.names.clone() {
            let Some(allocation) = state.allocation(id) else {
                self.losses.insert(SummaryLoss::ResourceProjection);
                continue;
            };
            let variants = allocation
                .object_state()
                .active_variants()
                .iter()
                .map(|(key, active)| VariantState {
                    offset: key.offset_bytes(),
                    access: key.access(),
                    alternatives: active
                        .alternatives()
                        .map(|v| Knowledge::Known(v.into_iter().collect()))
                        .unwrap_or(Knowledge::Unknown),
                })
                .collect();
            let payloads = allocation
                .object_state()
                .resource_payloads()
                .iter()
                .map(|(key, value)| PayloadState {
                    offset: key.offset_bytes(),
                    access: key.access(),
                    state: match value {
                        MovePathState::Moved => SummaryMovePath::Moved,
                        MovePathState::Unknown => SummaryMovePath::Unknown,
                        MovePathState::Available(payload) => SummaryMovePath::Available {
                            pointer: Box::new(self.pointer(payload.pointer())),
                            permission: Box::new(self.permission(payload.permission())),
                        },
                    },
                })
                .collect();
            let storage = match (&name, id) {
                (ResourceName::Input { .. }, _) => ResourceStorage::Input,
                (_, AbstractAllocationId::VirAllocationSite(_)) => ResourceStorage::Heap,
                (_, AbstractAllocationId::SummaryInstance { .. }) => ResourceStorage::Heap,
                (_, AbstractAllocationId::VirLocalStorageSite(_)) => {
                    ResourceStorage::ReturnedStorage
                }
                _ => {
                    self.losses.insert(SummaryLoss::ResourceProjection);
                    ResourceStorage::Unknown
                }
            };
            resources.push(ResourcePostState {
                name,
                storage,
                region: allocation.region(),
                size: allocation.size_bytes(),
                alignment: allocation.alignment().bytes(),
                liveness: allocation.liveness(),
                ownership: allocation.ownership(),
                initialization: allocation.initialization().clone(),
                validity: allocation.valid_value_bytes().clone(),
                scalar_contents: allocation.scalar_contents(),
                bool_origins: allocation
                    .scalar_contents()
                    .into_iter()
                    .filter_map(|(bytes, access, _)| {
                        Some((
                            bytes,
                            access,
                            self.bool_origin(allocation.bool_origin(bytes, access)?)?,
                        ))
                    })
                    .collect(),
                scalar_origins: allocation
                    .scalar_contents()
                    .into_iter()
                    .filter_map(|(bytes, access, _)| {
                        let origin = allocation.scalar_origin(bytes, access)?;
                        Some((bytes, access, self.scalar_origin(origin)?))
                    })
                    .collect(),
                variants,
                payloads,
                object_precise: allocation.object_state().is_precise(),
            });
        }
        resources.sort_by(|a, b| a.name.cmp(&b.name));
        resources
    }
    fn guard(&mut self, state: &ResourceState) -> Vec<SummaryGuard> {
        let mut guard = Vec::new();
        for fact in state.path_condition().facts().into_iter().flatten() {
            let mapped = match *fact {
                PathFact::Boolean { value, expected } => match self.aliases.get(&value) {
                    Some(ScalarTerm::Input(parameter))
                        if self.function.signature.parameters[*parameter] == VirType::Bool =>
                    {
                        Some(SummaryGuard::Boolean {
                            parameter: *parameter,
                            expected,
                        })
                    }
                    _ => self.comparison_guard(value, expected),
                },
                PathFact::Comparison {
                    predicate,
                    left,
                    right,
                } => self
                    .aliases
                    .get(&left)
                    .cloned()
                    .zip(self.aliases.get(&right).cloned())
                    .map(|(left, right)| SummaryGuard::Compare {
                        predicate,
                        left,
                        right,
                    }),
            };
            if let Some(mapped) = mapped {
                if !guard.contains(&mapped) {
                    guard.push(mapped);
                }
            } else {
                self.losses.insert(SummaryLoss::GuardProjection);
            }
        }
        // Conditional calls can restrict pre snapshots through the canonical
        // difference domain (without inventing literal SSA IDs). Export the
        // representable bounds so wrappers retain those numeric input guards.
        for bound in state.relations().bounds() {
            let input = |id| {
                self.aliases
                    .get(&id)
                    .filter(|term| matches!(term, ScalarTerm::Input(_)))
                    .cloned()
            };
            let mapped = match (bound.left, bound.right) {
                (Some(id), None) => u64::try_from(bound.bound)
                    .ok()
                    .filter(|n| *n < u64::MAX)
                    .and_then(|n| {
                        Some(SummaryGuard::Compare {
                            predicate: VirIntegerPredicate::LessOrEqual,
                            left: input(id)?,
                            right: ScalarTerm::Constant(n),
                        })
                    }),
                (None, Some(id)) => bound
                    .bound
                    .checked_neg()
                    .and_then(|n| u64::try_from(n).ok())
                    .filter(|n| *n > 0)
                    .and_then(|n| {
                        Some(SummaryGuard::Compare {
                            predicate: VirIntegerPredicate::GreaterOrEqual,
                            left: input(id)?,
                            right: ScalarTerm::Constant(n),
                        })
                    }),
                (Some(a), Some(b)) if a != b && bound.bound == 0 => {
                    input(a)
                        .zip(input(b))
                        .map(|(left, right)| SummaryGuard::Compare {
                            predicate: VirIntegerPredicate::LessOrEqual,
                            left,
                            right,
                        })
                }
                _ => None,
            };
            if let Some(mapped) = mapped
                && !guard.contains(&mapped)
            {
                guard.push(mapped);
            }
        }
        guard
    }
    fn comparison_guard(&self, value: VirValueId, expected: bool) -> Option<SummaryGuard> {
        for block in &self.function.blocks {
            for instruction in &block.instructions {
                if let VirInstruction::Compare {
                    result,
                    predicate,
                    left,
                    right,
                } = instruction.instruction
                    && result.id == value
                {
                    let predicate = if expected {
                        predicate
                    } else {
                        match predicate {
                            VirIntegerPredicate::Equal => VirIntegerPredicate::NotEqual,
                            VirIntegerPredicate::NotEqual => VirIntegerPredicate::Equal,
                            VirIntegerPredicate::LessThan => VirIntegerPredicate::GreaterOrEqual,
                            VirIntegerPredicate::LessOrEqual => VirIntegerPredicate::GreaterThan,
                            VirIntegerPredicate::GreaterThan => VirIntegerPredicate::LessOrEqual,
                            VirIntegerPredicate::GreaterOrEqual => VirIntegerPredicate::LessThan,
                        }
                    };
                    return Some(SummaryGuard::Compare {
                        predicate,
                        left: self.aliases.get(&left)?.clone(),
                        right: self.aliases.get(&right)?.clone(),
                    });
                }
            }
        }
        None
    }
}

fn provenance(value: AbstractValue) -> AbstractProvenance {
    match value {
        AbstractValue::Pointer(p) => p.provenance(),
        AbstractValue::Permission(p) => p.provenance(),
        _ => AbstractProvenance::Unknown,
    }
}

/// Only unconditional equalities: signature slots, literal definitions, and a
/// block parameter whose EVERY incoming argument names the same expression.
/// No path-refined constant is substituted into its own guard.
pub(crate) fn aliases(function: &VirFunction) -> BTreeMap<VirValueId, ScalarTerm> {
    let entry = function
        .blocks
        .iter()
        .find(|b| b.id == function.entry)
        .unwrap();
    let mut aliases: BTreeMap<_, _> = entry
        .parameters
        .iter()
        .enumerate()
        .map(|(i, p)| (p.id, ScalarTerm::Input(i)))
        .collect();
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let VirInstruction::Constant {
                result,
                value: VirConstant::U64(value),
            } = instruction.instruction
            {
                aliases.insert(result.id, ScalarTerm::Constant(value));
            }
        }
    }
    let mut incoming = BTreeMap::<VirValueId, Vec<VirValueId>>::new();
    let blocks: BTreeMap<_, _> = function.blocks.iter().map(|b| (b.id, b)).collect();
    for block in &function.blocks {
        let edges = match &block.terminator.terminator {
            VirTerminator::Jump { target } => vec![target],
            VirTerminator::Branch {
                then_target,
                else_target,
                ..
            } => vec![then_target, else_target],
            VirTerminator::Return { .. } => Vec::new(),
        };
        for edge in edges {
            for (parameter, argument) in blocks[&edge.block].parameters.iter().zip(&edge.arguments)
            {
                incoming.entry(parameter.id).or_default().push(*argument);
            }
        }
    }
    // A cyclic phi web is an alias only when ALL of its terminal definitions
    // have the same known origin, with at least one real seed. Do not equate
    // values by intervals or ignore a nontrivial definition on a back edge.
    // This handles n' = phi(n, n') without treating i' = phi(0, i+1) as 0.
    for &parameter in incoming.keys() {
        if aliases.contains_key(&parameter) {
            continue;
        }
        let mut pending = vec![parameter];
        let mut seen = BTreeSet::new();
        let mut origin = None;
        let mut valid = true;
        while let Some(value) = pending.pop() {
            if !seen.insert(value) {
                continue;
            }
            if let Some(term) = aliases.get(&value) {
                if origin.as_ref().is_some_and(|old| old != term) {
                    valid = false;
                    break;
                }
                origin = Some(term.clone());
            } else if let Some(arguments) = incoming.get(&value) {
                pending.extend(arguments);
            } else {
                valid = false;
                break;
            }
        }
        if valid && let Some(origin) = origin {
            aliases.insert(parameter, origin);
        }
    }
    aliases
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_observation_origins_never_project_as_entry_cells() {
        use crate::verifier::resource::{
            BoolOrigin, ScalarCellSnapshot, ScalarOrigin, ScalarOriginCell, ScalarOriginRoot,
        };
        let output = crate::analyze(&crate::SourceFile::from_text(
            "origin.nera",
            "fn main()->u64 { return 0; }",
        ));
        let resolved = output.vir().unwrap().resolve().unwrap();
        let function = &resolved.runtime().functions[0];
        let observation = ScalarCellSnapshot {
            epoch: 1,
            allocation: AbstractAllocationId::new(0),
            bytes: ByteRange::new(0, 8).unwrap(),
            access: crate::VirMemoryAccess::core_u64(),
        };
        let projector = Projector {
            function,
            path_parameters: Vec::new(),
            aliases: aliases(function),
            result_aliases: BTreeMap::new(),
            result_offset_aliases: BTreeMap::new(),
            names: BTreeMap::from([(
                observation.allocation,
                ResourceName::Input {
                    parameter: 0,
                    payload_offsets: vec![],
                },
            )]),
            loans: BTreeMap::new(),
            stored_loans: BTreeMap::new(),
            losses: BTreeSet::new(),
        };
        let mut origin = ScalarOrigin {
            first: ScalarOriginCell {
                root: ScalarOriginRoot::Snapshot(observation),
                initial_lower: 0,
                initial_upper: 42,
            },
            scale: 1,
            second: None,
            addend: 0,
        };
        assert!(projector.scalar_origin(origin).is_none());
        assert!(
            projector
                .bool_origin(BoolOrigin::Snapshot(observation))
                .is_none()
        );
        let snapshot = origin;
        origin.first.root = ScalarOriginRoot::Cell {
            allocation: observation.allocation,
            bytes: observation.bytes,
            access: observation.access,
        };
        assert!(projector.scalar_origin(origin).is_some());
        assert!(
            projector
                .scalar_origin(origin.sum(snapshot).unwrap())
                .is_none()
        );
        let mut allocation = crate::AbstractAllocation::new_local(8, 8).unwrap();
        allocation.mark_initialized(observation.bytes).unwrap();
        allocation.mark_valid(observation.bytes).unwrap();
        allocation.record_scalar_content(
            observation.bytes,
            observation.access,
            AbstractValue::U64(crate::U64Interval::new(0, 42).unwrap()),
        );
        allocation.set_scalar_origin(observation.bytes, observation.access, origin);
        let mut transport = crate::verifier::resource::ScalarOriginTransport::default();
        transport
            .allocation(
                &mut allocation,
                &mut 1,
                &mut crate::predicate_logic::LogicBudget::default(),
            )
            .unwrap();
        assert!(
            projector
                .scalar_origin(
                    allocation
                        .scalar_origin(observation.bytes, observation.access)
                        .unwrap()
                )
                .is_none()
        );
    }

    #[test]
    fn conditional_borrow_world_rejects_swapped_guard_pointer_or_authority() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "conditional-world.nera",
            "fn main()->u64 { let a=1; let b=2; let r=choose(true,&a,&b); return *r; }
             fn choose(flag:bool,a:&u64,b:&u64)->&u64 {
                 if flag { return a; } else { return b; }
             }",
        ));
        let resolved = output.vir().unwrap().resolve().unwrap();
        let report = crate::verify_program(&resolved, Default::default()).unwrap();
        assert!(report.is_memory_checked_core0());
        let function = &resolved.runtime().functions[1];
        let abi = &resolved
            .runtime()
            .abis
            .function(function.id)
            .unwrap()
            .signature;
        let summary = report.functions()[&function.id].summary();
        let Knowledge::Known(alternatives) = &summary.normal_returns else {
            panic!("closed body has return worlds");
        };
        let alternative = alternatives
            .iter()
            .find(|alternative| {
                alternative.guard.contains(&SummaryGuard::Boolean {
                    parameter: 0,
                    expected: true,
                })
            })
            .unwrap();
        let values = &alternative.worlds[0].values;
        assert!(conditional_borrow_world_matches(
            abi,
            &alternative.guard,
            values,
            resolved.runtime().memory
        ));

        let swapped_guard = [SummaryGuard::Boolean {
            parameter: 0,
            expected: false,
        }];
        assert!(!conditional_borrow_world_matches(
            abi,
            &swapped_guard,
            values,
            resolved.runtime().memory
        ));

        let true_relation = abi
            .borrow_result_alternatives()
            .iter()
            .find(|candidate| {
                candidate.guard.contains(&BorrowGuardAtom::Boolean {
                    parameter: 0,
                    expected: true,
                })
            })
            .unwrap()
            .relation;
        let false_relation = abi
            .borrow_result_alternatives()
            .iter()
            .find(|candidate| {
                candidate.guard.contains(&BorrowGuardAtom::Boolean {
                    parameter: 0,
                    expected: false,
                })
            })
            .unwrap()
            .relation;
        let output_slots = abi.results()[0].result_slots();
        let wrong_slots = abi.parameters()[false_relation.parameter as usize].parameter_slots();

        let mut pointer_swapped = values.clone();
        let pointer = pointer_swapped
            .iter_mut()
            .find(|mapping| {
                mapping.coordinate.coordinate == ValueCoordinate::Result(output_slots[0] as usize)
            })
            .unwrap();
        let SummaryValue::Pointer(pointer) = &mut pointer.value else {
            panic!("borrow result has a pointer slot");
        };
        pointer.resource = Knowledge::Known(ResourceName::Input {
            parameter: wrong_slots[0] as usize,
            payload_offsets: Vec::new(),
        });
        assert!(!conditional_borrow_world_matches(
            abi,
            &alternative.guard,
            &pointer_swapped,
            resolved.runtime().memory
        ));

        let mut authority_swapped = values.clone();
        let permission = authority_swapped
            .iter_mut()
            .find(|mapping| {
                mapping.coordinate.coordinate
                    == ValueCoordinate::Result(*output_slots.last().unwrap() as usize)
            })
            .unwrap();
        let SummaryValue::Permission(permission) = &mut permission.value else {
            panic!("borrow result has a permission slot");
        };
        permission.authority = SummaryAuthority::InputLoan(*wrong_slots.last().unwrap() as usize);
        assert_ne!(true_relation.parameter, false_relation.parameter);
        assert!(!conditional_borrow_world_matches(
            abi,
            &alternative.guard,
            &authority_swapped,
            resolved.runtime().memory
        ));
    }

    // The surface still gates owning-enum interfaces. Exercise the same
    // resource projector on REAL final CFG instruction cases of supported
    // local enums, without opening that unrelated source-language boundary.
    #[test]
    fn enum_tag_payload_projection_is_atomic_for_real_cfg_cases() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "enum.nera",
            "enum Item { Empty, Full(Own<u64>), }
            fn coin(flag:bool)->bool { if flag { return true; } return false; }
            fn main()->u64 { return run(true); }
            fn run(flag:bool)->u64 { let p=alloc<Item>(1);
                if coin(flag) { let q=alloc<u64>(1); *q=42; *p=Item::Full(q); }
                else { *p=Item::Empty; } free(p); return 42; }",
        ));
        let resolved = output.vir().unwrap().resolve().unwrap();
        let report = crate::verify_program(&resolved, Default::default()).unwrap();
        let function = resolved
            .runtime()
            .functions
            .iter()
            .find(|f| f.name == "run")
            .unwrap();
        let cfg = report.functions()[&function.id].cfg();
        let mut observed = BTreeSet::new();
        for block in cfg.blocks().values() {
            for conditional in block.instruction_conditional_states() {
                for state in conditional.cases() {
                    for (&id, allocation) in state.allocations() {
                        for active in allocation.object_state().active_variants().values() {
                            let Some(tags) = active.alternatives() else {
                                continue;
                            };
                            if tags.len() != 1 {
                                continue;
                            }
                            let mut projector = Projector {
                                function,
                                path_parameters: Vec::new(),
                                aliases: aliases(function),
                                result_aliases: BTreeMap::new(),
                                result_offset_aliases: BTreeMap::new(),
                                names: BTreeMap::new(),
                                loans: BTreeMap::new(),
                                stored_loans: BTreeMap::new(),
                                losses: BTreeSet::new(),
                            };
                            projector.discover(
                                state,
                                AbstractProvenance::Known(id),
                                ResourceName::Fresh(0),
                            );
                            let resources = projector.resources(state);
                            let object = resources
                                .iter()
                                .find(|r| r.name == ResourceName::Fresh(0))
                                .unwrap();
                            assert_eq!(
                                object.variants.len(),
                                allocation.object_state().active_variants().len()
                            );
                            assert_eq!(
                                object.payloads.len(),
                                allocation.object_state().resource_payloads().len()
                            );
                            for (projected, original) in object
                                .payloads
                                .iter()
                                .zip(allocation.object_state().resource_payloads().values())
                            {
                                assert_eq!(
                                    matches!(projected.state, SummaryMovePath::Available { .. }),
                                    matches!(original, MovePathState::Available(_))
                                );
                            }
                            let tag = *tags.iter().next().unwrap();
                            assert!(
                                object
                                    .variants
                                    .iter()
                                    .any(|v| v.alternatives == Knowledge::Known(vec![tag]))
                            );
                            observed.insert(
                                resolved.runtime().memory.variant(tag).unwrap().discriminant,
                            );
                        }
                    }
                }
            }
        }
        assert_eq!(observed, [0, 1].into());
    }
}
