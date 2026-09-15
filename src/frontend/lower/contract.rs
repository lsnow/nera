//! Type-derived interface contracts and typed Spec HIR to Spec VIR conversion.
//! This producer never derives or trusts body-derived verifier summaries.
use super::{
    ByteSpan, FrontendFailure, HirProgram, HirSpecBinderOwner, HirSpecClauseOwner,
    HirSpecContractPosition, HirSpecLocation, HirSpecSnapshot, HirSpecTermKind, HirTrustPolicyKind,
    HirTrustScope, HirTypeId, HirTypeKind, LoweredMemorySchema, RuntimeVirProgram, VirAbiValue,
    VirContractAccess, VirContractFree, VirContractId, VirContractInitialization,
    VirContractLiveness, VirContractOwnership, VirContractPermission, VirContractPointer,
    VirContractPosition, VirContractResourceSummary, VirFunctionId, VirLocation, VirPredicate,
    VirPredicateId, VirRegionId, VirSourceId, VirSourceMap, VirSpecBinder, VirSpecBinderId,
    VirSpecBinderOwner, VirSpecClause, VirSpecClauseId, VirSpecClauseKind, VirSpecClauseOrigin,
    VirSpecClauseOwner, VirSpecEnvironment, VirSpecLocation, VirSpecProve, VirSpecProveId,
    VirSpecSnapshot, VirSpecTerm, VirSpecTermId, VirSpecTermKind, VirSpecType, VirTrustEntry,
    VirTrustEntryId, VirTrustPolicyKind, VirTrustScope, hir_parameter_abi_slot, invalid_hir,
};

pub(super) fn infer_contracts(
    hir: &HirProgram,
    memory: &LoweredMemorySchema,
    runtime: &RuntimeVirProgram,
    source_map: &VirSourceMap,
    local_specs: &[super::local_spec::LocalSpec],
    loop_specs: &[super::loop_spec::LoopSpec],
    spec_sources: &std::collections::BTreeMap<crate::HirModuleId, VirSourceId>,
) -> Result<VirSpecEnvironment, FrontendFailure> {
    let mut specs = VirSpecEnvironment::implicit(runtime);
    for function in hir
        .functions()
        .iter()
        .filter(|function| function.generic_parameters.is_empty())
    {
        let runtime_function = runtime
            .functions
            .iter()
            .find(|candidate| candidate.id.get() == function.id.get())
            .ok_or_else(|| invalid_hir(function.span))?;
        let origin = source_map
            .origin_at(VirLocation::FunctionEntry {
                function: runtime_function.id,
            })
            .ok_or_else(|| invalid_hir(function.span))?
            .id;
        if specs.contract(runtime_function.contract).is_none() {
            return Err(invalid_hir(function.span));
        }

        let function_abi = runtime
            .abis
            .function(runtime_function.id)
            .ok_or_else(|| invalid_hir(function.span))?;
        for binding in function_abi.signature.parameters() {
            if binding.interface().transfer == crate::VirInterfaceTransfer::Move
                && let VirAbiValue::Pointer { access, pointee } = binding.value()
                && matches!(
                    memory.schema().kind(access.ty),
                    Some(crate::VirMemoryTypeKind::Pointer {
                        kind: crate::VirPointerKind::Own,
                        ..
                    })
                )
            {
                let [pointer_slot, _permission_slot] = binding.parameter_slots() else {
                    return Err(invalid_hir(function.span));
                };
                add_inferred_own_clause(
                    &mut specs,
                    InferredOwnClause {
                        contract: runtime_function.contract,
                        position: VirContractPosition::Requires,
                        pointer_slot: *pointer_slot as usize,
                        pointee: *pointee,
                        origin,
                        source_span: function.span,
                    },
                    memory,
                )?;
            }
            if binding.interface().storage == crate::VirInterfaceStorage::Indirect
                && let VirAbiValue::IndirectAggregate { access } = binding.value()
            {
                let result_initialization =
                    if binding.interface().transfer == crate::VirInterfaceTransfer::Move {
                        VirContractInitialization::Uninitialized
                    } else {
                        VirContractInitialization::Initialized
                    };
                add_inferred_indirect_abi_clauses(
                    &mut specs,
                    InferredIndirectAbiClauses {
                        contract: runtime_function.contract,
                        access: *access,
                        parameter_slots: binding.parameter_slots(),
                        result_slots: binding.result_slots(),
                        parameter_initialization: VirContractInitialization::Initialized,
                        result_initialization,
                        origin,
                        source_span: function.span,
                    },
                    memory,
                )?;
            }
        }
        if let Some(binding) = function_abi.signature.results().first()
            && binding.interface().transfer == crate::VirInterfaceTransfer::Move
            && let VirAbiValue::Pointer { access, pointee } = binding.value()
            && matches!(
                memory.schema().kind(access.ty),
                Some(crate::VirMemoryTypeKind::Pointer {
                    kind: crate::VirPointerKind::Own,
                    ..
                })
            )
        {
            let [pointer_slot, _permission_slot] = binding.result_slots() else {
                return Err(invalid_hir(function.span));
            };
            add_inferred_own_clause(
                &mut specs,
                InferredOwnClause {
                    contract: runtime_function.contract,
                    position: VirContractPosition::Ensures,
                    pointer_slot: *pointer_slot as usize,
                    pointee: *pointee,
                    origin,
                    source_span: function.span,
                },
                memory,
            )?;
        }
        if let Some(binding) = function_abi.signature.results().first()
            && binding.interface().storage == crate::VirInterfaceStorage::Indirect
            && let VirAbiValue::IndirectAggregate { access } = binding.value()
        {
            add_inferred_indirect_abi_clauses(
                &mut specs,
                InferredIndirectAbiClauses {
                    contract: runtime_function.contract,
                    access: *access,
                    parameter_slots: binding.parameter_slots(),
                    result_slots: binding.result_slots(),
                    parameter_initialization: VirContractInitialization::Uninitialized,
                    result_initialization: VirContractInitialization::Initialized,
                    origin,
                    source_span: function.span,
                },
                memory,
            )?;
        }
    }
    lower_hir_specs(
        hir,
        memory,
        source_map,
        &mut specs,
        local_specs,
        loop_specs,
        spec_sources,
    )?;
    for invariant in &hir.specs().loop_invariants {
        let id = crate::VirSpecLoopInvariantId::new(invariant.id.get());
        let mapped = loop_specs
            .iter()
            .find(|s| {
                s.function.get() == invariant.function.get() && s.loop_id == invariant.loop_id
            })
            .ok_or_else(|| invalid_hir(invariant.span))?;
        let mut boundary = mapped.boundary.clone();
        let function = runtime
            .functions
            .iter()
            .find(|f| f.id == mapped.function)
            .ok_or_else(|| invalid_hir(invariant.span))?;
        (boundary.entries, boundary.back_edges, boundary.exits) = boundary.edges(function);
        let clause = specs
            .clauses()
            .iter()
            .find(|c| c.owner == VirSpecClauseOwner::LoopInvariant(id))
            .ok_or_else(|| invalid_hir(invariant.span))?;
        let lowered = crate::VirSpecLoopInvariant {
            id,
            function: mapped.function,
            location: clause.location,
            clause: clause.id,
            origin: source_map
                .user_origin(
                    *spec_sources
                        .get(&hir.function_by_id(invariant.function).unwrap().module)
                        .unwrap(),
                    invariant.span,
                )
                .ok_or_else(|| invalid_hir(invariant.span))?,
            boundary: Some(boundary),
        };
        specs.loop_invariants_mut().push(lowered);
    }
    Ok(specs)
}

#[derive(Clone, Copy)]
struct InferredOwnClause {
    contract: VirContractId,
    position: VirContractPosition,
    pointer_slot: usize,
    pointee: crate::VirMemoryAccess,
    origin: crate::VirOriginId,
    source_span: ByteSpan,
}

fn add_inferred_own_clause(
    specs: &mut VirSpecEnvironment,
    clause: InferredOwnClause,
    memory: &LoweredMemorySchema,
) -> Result<(), FrontendFailure> {
    let layout = memory
        .schema()
        .layout(clause.pointee.layout)
        .filter(|layout| layout.ty == clause.pointee.ty)
        .ok_or_else(|| invalid_hir(clause.source_span))?;
    let (pointer, permission) = {
        let contract = specs
            .contract(clause.contract)
            .ok_or_else(|| invalid_hir(clause.source_span))?;
        (
            contract
                .binder(clause.position, clause.pointer_slot)
                .ok_or_else(|| invalid_hir(clause.source_span))?,
            contract
                .binder(clause.position, clause.pointer_slot + 1)
                .ok_or_else(|| invalid_hir(clause.source_span))?,
        )
    };
    let resource = specs
        .contract_mut(clause.contract)
        .ok_or_else(|| invalid_hir(clause.source_span))?
        .add_resource();
    specs
        .add_contract_clause(
            clause.contract,
            clause.position,
            VirSpecClauseOrigin::InferredType {
                origin: clause.origin,
            },
            VirSpecClauseKind::Resource(VirContractResourceSummary {
                resource,
                region: VirRegionId::new(0),
                size_bytes: layout.size_bytes,
                alignment: layout.alignment,
                liveness: VirContractLiveness::Live,
                ownership: VirContractOwnership::Owned,
                initialization: VirContractInitialization::Initialized,
                pointers: vec![VirContractPointer {
                    binder: pointer,
                    offset_lower: 0,
                    offset_upper: 0,
                    alignment: layout.alignment,
                }],
                permissions: vec![VirContractPermission {
                    binder: permission,
                    start_byte: 0,
                    end_byte: layout.size_bytes,
                    access: VirContractAccess::Write,
                    free: VirContractFree::Yes,
                }],
            }),
        )
        .ok_or_else(|| invalid_hir(clause.source_span))?;
    Ok(())
}

#[derive(Clone, Copy)]
struct InferredIndirectAbiClauses<'slots> {
    contract: VirContractId,
    access: crate::VirMemoryAccess,
    parameter_slots: &'slots [u32],
    result_slots: &'slots [u32],
    parameter_initialization: VirContractInitialization,
    result_initialization: VirContractInitialization,
    origin: crate::VirOriginId,
    source_span: ByteSpan,
}

fn add_inferred_indirect_abi_clauses(
    specs: &mut VirSpecEnvironment,
    clauses: InferredIndirectAbiClauses<'_>,
    memory: &LoweredMemorySchema,
) -> Result<(), FrontendFailure> {
    let [pointer_slot, permission_slot] = clauses.parameter_slots else {
        return Err(invalid_hir(clauses.source_span));
    };
    let [result_permission_slot] = clauses.result_slots else {
        return Err(invalid_hir(clauses.source_span));
    };
    let layout = memory
        .schema()
        .layout(clauses.access.layout)
        .filter(|layout| layout.ty == clauses.access.ty)
        .ok_or_else(|| invalid_hir(clauses.source_span))?;
    let (pointer, parameter_permission, result_permission) = {
        let contract = specs
            .contract(clauses.contract)
            .ok_or_else(|| invalid_hir(clauses.source_span))?;
        (
            contract
                .binder(VirContractPosition::Requires, *pointer_slot as usize)
                .ok_or_else(|| invalid_hir(clauses.source_span))?,
            contract
                .binder(VirContractPosition::Requires, *permission_slot as usize)
                .ok_or_else(|| invalid_hir(clauses.source_span))?,
            contract
                .binder(
                    VirContractPosition::Ensures,
                    *result_permission_slot as usize,
                )
                .ok_or_else(|| invalid_hir(clauses.source_span))?,
        )
    };
    let resource = specs
        .contract_mut(clauses.contract)
        .ok_or_else(|| invalid_hir(clauses.source_span))?
        .add_resource();
    let origin = VirSpecClauseOrigin::InferredType {
        origin: clauses.origin,
    };
    specs
        .add_contract_clause(
            clauses.contract,
            VirContractPosition::Requires,
            origin,
            VirSpecClauseKind::Resource(VirContractResourceSummary {
                resource,
                region: VirRegionId::new(0),
                size_bytes: layout.size_bytes,
                alignment: layout.alignment,
                liveness: VirContractLiveness::Live,
                ownership: VirContractOwnership::Local,
                initialization: clauses.parameter_initialization,
                pointers: vec![VirContractPointer {
                    binder: pointer,
                    offset_lower: 0,
                    offset_upper: 0,
                    alignment: layout.alignment,
                }],
                permissions: vec![VirContractPermission {
                    binder: parameter_permission,
                    start_byte: 0,
                    end_byte: layout.size_bytes,
                    access: VirContractAccess::Write,
                    free: VirContractFree::No,
                }],
            }),
        )
        .ok_or_else(|| invalid_hir(clauses.source_span))?;
    specs
        .add_contract_clause(
            clauses.contract,
            VirContractPosition::Ensures,
            origin,
            VirSpecClauseKind::Resource(VirContractResourceSummary {
                resource,
                region: VirRegionId::new(0),
                size_bytes: layout.size_bytes,
                alignment: layout.alignment,
                liveness: VirContractLiveness::Live,
                ownership: VirContractOwnership::Local,
                initialization: clauses.result_initialization,
                pointers: Vec::new(),
                permissions: vec![VirContractPermission {
                    binder: result_permission,
                    start_byte: 0,
                    end_byte: layout.size_bytes,
                    access: VirContractAccess::Write,
                    free: VirContractFree::No,
                }],
            }),
        )
        .ok_or_else(|| invalid_hir(clauses.source_span))?;
    Ok(())
}

fn lower_hir_specs(
    hir: &HirProgram,
    memory: &LoweredMemorySchema,
    source_map: &VirSourceMap,
    specs: &mut VirSpecEnvironment,
    local_specs: &[super::local_spec::LocalSpec],
    loop_specs: &[super::loop_spec::LoopSpec],
    spec_sources: &std::collections::BTreeMap<crate::HirModuleId, VirSourceId>,
) -> Result<(), FrontendFailure> {
    let spec_source_origin =
        |module, span| source_map.user_origin(*spec_sources.get(&module)?, span);
    let clause_base =
        u32::try_from(specs.clauses().len()).map_err(|_| invalid_hir(hir.entry_function().span))?;

    for predicate in hir.predicates() {
        let origin = spec_source_origin(predicate.module, predicate.span)
            .ok_or_else(|| invalid_hir(predicate.span))?;
        specs.predicates_mut().push(VirPredicate {
            id: VirPredicateId::new(predicate.id.get()),
            name: predicate.name.clone(),
            binders: predicate
                .binders
                .iter()
                .map(|binder| VirSpecBinderId::new(binder.get()))
                .collect(),
            origin,
            body: match predicate.body {
                Some(clause) => Some(
                    shifted_clause_id(clause_base, clause)
                        .ok_or_else(|| invalid_hir(predicate.span))?,
                ),
                None => None,
            },
        });
    }

    for binder in &hir.specs().binders {
        let origin = spec_source_origin(binder_module(hir, binder.owner), binder.span)
            .ok_or_else(|| invalid_hir(binder.span))?;
        specs.binders_mut().push(VirSpecBinder {
            id: VirSpecBinderId::new(binder.id.get()),
            owner: match binder.owner {
                HirSpecBinderOwner::Clause(clause) => VirSpecBinderOwner::Clause(
                    shifted_clause_id(clause_base, clause)
                        .ok_or_else(|| invalid_hir(binder.span))?,
                ),
                HirSpecBinderOwner::Predicate(predicate) => {
                    VirSpecBinderOwner::Predicate(VirPredicateId::new(predicate.get()))
                }
            },
            name: binder.name.clone(),
            ty: lower_spec_type(hir, binder.ty).ok_or_else(|| invalid_hir(binder.span))?,
            origin,
        });
    }

    for term in &hir.specs().terms {
        let origin = spec_source_origin(clause_module(hir, term.clause), term.span)
            .ok_or_else(|| invalid_hir(term.span))?;
        specs.terms_mut().push(VirSpecTerm {
            id: VirSpecTermId::new(term.id.get()),
            clause: shifted_clause_id(clause_base, term.clause)
                .ok_or_else(|| invalid_hir(term.span))?,
            ty: lower_spec_type(hir, term.ty).ok_or_else(|| invalid_hir(term.span))?,
            kind: if let HirSpecTermKind::Snapshot(HirSpecSnapshot::Local { local, .. }) = term.kind
                && let HirSpecLocation::Statement { prove, .. } =
                    hir.specs().clauses[term.clause.index()].location
            {
                let binding = local_specs
                    .iter()
                    .find(|s| s.prove == prove)
                    .ok_or_else(|| invalid_hir(term.span))?;
                VirSpecTermKind::Snapshot(binding.scalar(
                    local,
                    lower_spec_type(hir, term.ty).ok_or_else(|| invalid_hir(term.span))?,
                    term.span,
                )?)
            } else if let HirSpecTermKind::Snapshot(HirSpecSnapshot::LoopEntry {
                function,
                loop_id,
                local,
            }) = term.kind
            {
                let binding = loop_specs
                    .iter()
                    .find(|s| s.function.get() == function.get() && s.loop_id == loop_id)
                    .and_then(|s| s.boundary.bindings.iter().find(|b| b.local == local.get()))
                    .ok_or_else(|| {
                        let mut failure = FrontendFailure::unsupported(
                            term.span,
                            "loop entry scalar is not retained at the header",
                        );
                        failure.source = hir
                            .function_by_id(function)
                            .map(|f| VirSourceId::new(f.module.get()));
                        failure
                    })?;
                VirSpecTermKind::Snapshot(VirSpecSnapshot::Value {
                    function: VirFunctionId::new(function.get()),
                    value: binding.entry,
                })
            } else if let HirSpecTermKind::Snapshot(HirSpecSnapshot::Local { local, function }) =
                term.kind
                && let HirSpecLocation::LoopHead { loop_id, .. } =
                    hir.specs().clauses[term.clause.index()].location
            {
                let binding = loop_specs
                    .iter()
                    .find(|s| s.function.get() == function.get() && s.loop_id == loop_id)
                    .and_then(|s| s.boundary.bindings.iter().find(|b| b.local == local.get()))
                    .ok_or_else(|| {
                        let mut failure = FrontendFailure::unsupported(
                            term.span,
                            "loop snapshot is not retained as a scalar head parameter",
                        );
                        failure.source = hir
                            .function_by_id(function)
                            .map(|f| VirSourceId::new(f.module.get()));
                        failure
                    })?;
                VirSpecTermKind::Snapshot(VirSpecSnapshot::Value {
                    function: VirFunctionId::new(function.get()),
                    value: binding.head,
                })
            } else {
                lower_spec_term_kind(hir, memory, &term.kind, term.span)?
            },
            origin,
        });
    }

    for assertion in &hir.specs().assertions {
        specs.assertions_mut().push(crate::VirSpecAssertion {
            id: crate::VirSpecAssertionId::new(assertion.id.get()),
            clause: shifted_clause_id(clause_base, assertion.clause)
                .ok_or_else(|| invalid_hir(assertion.span))?,
            kind: lower_assertion(
                hir,
                memory,
                &assertion.kind,
                assertion.span,
                if let HirSpecLocation::Statement { prove, .. } =
                    hir.specs().clauses[assertion.clause.index()].location
                {
                    Some(
                        local_specs
                            .iter()
                            .find(|s| s.prove == prove)
                            .ok_or_else(|| invalid_hir(assertion.span))?,
                    )
                } else {
                    None
                },
                if let HirSpecLocation::LoopHead { function, loop_id } =
                    hir.specs().clauses[assertion.clause.index()].location
                {
                    Some(
                        loop_specs
                            .iter()
                            .find(|s| s.function.get() == function.get() && s.loop_id == loop_id)
                            .ok_or_else(|| invalid_hir(assertion.span))?,
                    )
                } else {
                    None
                },
            )?,
            origin: spec_source_origin(clause_module(hir, assertion.clause), assertion.span)
                .ok_or_else(|| invalid_hir(assertion.span))?,
        });
    }

    for clause in &hir.specs().clauses {
        let origin = spec_source_origin(clause_module(hir, clause.id), clause.span)
            .ok_or_else(|| invalid_hir(clause.span))?;
        specs.clauses_mut().push(VirSpecClause {
            id: shifted_clause_id(clause_base, clause.id)
                .ok_or_else(|| invalid_hir(clause.span))?,
            owner: match clause.owner {
                HirSpecClauseOwner::Contract { contract, position } => {
                    VirSpecClauseOwner::Contract {
                        contract: VirContractId::new(contract.get()),
                        position: match position {
                            HirSpecContractPosition::Requires => VirContractPosition::Requires,
                            HirSpecContractPosition::Ensures => VirContractPosition::Ensures,
                        },
                    }
                }
                HirSpecClauseOwner::Prove(prove) => {
                    VirSpecClauseOwner::Prove(VirSpecProveId::new(prove.get()))
                }
                HirSpecClauseOwner::TrustEntry(entry) => {
                    VirSpecClauseOwner::TrustEntry(VirTrustEntryId::new(entry.get()))
                }
                HirSpecClauseOwner::LoopInvariant(invariant) => VirSpecClauseOwner::LoopInvariant(
                    crate::VirSpecLoopInvariantId::new(invariant.get()),
                ),
            },
            location: lower_spec_location(clause.location, local_specs, loop_specs)
                .ok_or_else(|| invalid_hir(clause.span))?,
            origin: VirSpecClauseOrigin::Explicit { origin },
            kind: match clause.root {
                crate::HirSpecRoot::Pure(root) => VirSpecClauseKind::Logic {
                    root: VirSpecTermId::new(root.get()),
                },
                crate::HirSpecRoot::Assertion(root) => VirSpecClauseKind::Assertion {
                    root: crate::VirSpecAssertionId::new(root.get()),
                },
            },
        });
    }

    for contract in hir.contracts() {
        let lowered = specs
            .contract_mut(VirContractId::new(contract.id.get()))
            .ok_or_else(|| invalid_hir(contract.span))?;
        for clause in &contract.clauses {
            lowered.clauses.push(
                shifted_clause_id(clause_base, *clause)
                    .ok_or_else(|| invalid_hir(contract.span))?,
            );
        }
    }

    for prove in &hir.specs().proves {
        let origin = spec_source_origin(clause_module(hir, prove.clause), prove.span)
            .ok_or_else(|| invalid_hir(prove.span))?;
        specs.proves_mut().push(VirSpecProve {
            id: VirSpecProveId::new(prove.id.get()),
            function: VirFunctionId::new(prove.function.get()),
            location: lower_spec_location(prove.location, local_specs, loop_specs)
                .ok_or_else(|| invalid_hir(prove.span))?,
            clause: shifted_clause_id(clause_base, prove.clause)
                .ok_or_else(|| invalid_hir(prove.span))?,
            origin,
        });
    }
    for entry in &hir.specs().trust_entries {
        let origin = spec_source_origin(clause_module(hir, entry.clause), entry.span)
            .ok_or_else(|| invalid_hir(entry.span))?;
        specs.trust_entries_mut().push(VirTrustEntry {
            id: VirTrustEntryId::new(entry.id.get()),
            scope: match entry.scope {
                HirTrustScope::FunctionEntry { function } => VirTrustScope::FunctionEntry {
                    function: VirFunctionId::new(function.get()),
                },
                HirTrustScope::FunctionResult { function } => VirTrustScope::FunctionResult {
                    function: VirFunctionId::new(function.get()),
                },
            },
            policy: match entry.policy {
                HirTrustPolicyKind::EntryPointAssumption => {
                    VirTrustPolicyKind::EntryPointAssumption
                }
                HirTrustPolicyKind::ForeignContract => VirTrustPolicyKind::ForeignContract,
                HirTrustPolicyKind::ExternallyVerified => VirTrustPolicyKind::ExternallyVerified,
            },
            clause: shifted_clause_id(clause_base, entry.clause)
                .ok_or_else(|| invalid_hir(entry.span))?,
            origin,
        });
    }
    Ok(())
}

fn clause_module(hir: &HirProgram, clause: crate::HirSpecClauseId) -> crate::HirModuleId {
    hir.function_by_id(hir.specs().clauses[clause.index()].location.function())
        .expect("validated clause owner")
        .module
}

fn binder_module(hir: &HirProgram, owner: HirSpecBinderOwner) -> crate::HirModuleId {
    match owner {
        HirSpecBinderOwner::Clause(clause) => clause_module(hir, clause),
        HirSpecBinderOwner::Predicate(predicate) => hir.predicates()[predicate.index()].module,
    }
}

pub(super) fn spec_source_spans(hir: &HirProgram, module: crate::HirModuleId) -> Vec<ByteSpan> {
    hir.predicates()
        .iter()
        .filter(|predicate| predicate.module == module)
        .map(|predicate| predicate.span)
        .chain(
            hir.specs()
                .binders
                .iter()
                .filter(|binder| binder_module(hir, binder.owner) == module)
                .map(|binder| binder.span),
        )
        .chain(
            hir.specs()
                .terms
                .iter()
                .filter(|term| clause_module(hir, term.clause) == module)
                .map(|term| term.span),
        )
        .chain(
            hir.specs()
                .assertions
                .iter()
                .filter(|assertion| clause_module(hir, assertion.clause) == module)
                .map(|assertion| assertion.span),
        )
        .chain(
            hir.specs()
                .clauses
                .iter()
                .filter(|clause| clause_module(hir, clause.id) == module)
                .map(|clause| clause.span),
        )
        .chain(
            hir.specs()
                .proves
                .iter()
                .filter(|prove| clause_module(hir, prove.clause) == module)
                .map(|prove| prove.span),
        )
        .chain(
            hir.specs()
                .trust_entries
                .iter()
                .filter(|entry| clause_module(hir, entry.clause) == module)
                .map(|entry| entry.span),
        )
        .chain(
            hir.specs()
                .loop_invariants
                .iter()
                .filter(|invariant| clause_module(hir, invariant.clause) == module)
                .map(|invariant| invariant.span),
        )
        .collect()
}

fn shifted_clause_id(
    base: u32,
    clause: crate::frontend::hir::HirSpecClauseId,
) -> Option<VirSpecClauseId> {
    base.checked_add(clause.get()).map(VirSpecClauseId::new)
}

fn lower_spec_type(hir: &HirProgram, ty: HirTypeId) -> Option<VirSpecType> {
    match hir.type_kind(ty)? {
        HirTypeKind::Bool => Some(VirSpecType::Bool),
        HirTypeKind::Integer(crate::frontend::hir::HirIntegerType::U64) => Some(VirSpecType::U64),
        HirTypeKind::Integer(crate::frontend::hir::HirIntegerType::Usize)
            if hir.data_layout().usize_size_bytes == 8 =>
        {
            Some(VirSpecType::U64)
        }
        _ => None,
    }
}

fn lower_assertion(
    hir: &HirProgram,
    memory: &LoweredMemorySchema,
    kind: &crate::HirSpecAssertionKind,
    span: ByteSpan,
    local: Option<&super::local_spec::LocalSpec>,
    loop_spec: Option<&super::loop_spec::LoopSpec>,
) -> Result<crate::VirSpecAssertionKind, FrontendFailure> {
    use crate::SpecAssertionKind as A;
    let term = |id: crate::HirSpecTermId| VirSpecTermId::new(id.get());
    let assertion = |id: crate::HirSpecAssertionId| crate::VirSpecAssertionId::new(id.get());
    let snapshot = |s, authority| {
        if let Some(local) = local {
            local.pointer(s, authority, span)
        } else if let Some(loop_spec) = loop_spec {
            super::local_spec::pointer_snapshot(
                loop_spec.function,
                &loop_spec.values,
                s,
                authority,
                span,
            )
        } else if authority {
            lower_authority_snapshot(hir, memory, s, span)
        } else {
            lower_snapshot(hir, memory, s, span)
        }
    };
    let claim = |c: &crate::SpecMemoryClaim<HirSpecSnapshot, crate::HirSpecTermId, HirTypeId>| -> Result<_, FrontendFailure> {
        Ok(crate::SpecMemoryClaim {
            pointer: snapshot(c.pointer, false)?,
            authority: snapshot(c.authority, true)?,
            start_bytes: term(c.start_bytes), end_bytes: term(c.end_bytes),
            layout: memory.access(c.layout, span)?, access: c.access,
        })
    };
    Ok(match kind {
        A::Footprint { write, range } => A::Footprint {
            write: *write,
            range: range
                .as_ref()
                .map(|r| {
                    Ok::<_, FrontendFailure>(crate::SpecMemoryRange {
                        pointer: snapshot(r.pointer, false)?,
                        start_bytes: term(r.start_bytes),
                        end_bytes: term(r.end_bytes),
                        layout: memory.access(r.layout, span)?,
                    })
                })
                .transpose()?,
        },
        A::Disjoint { left, right } => {
            let range = |r: &crate::SpecMemoryRange<
                HirSpecSnapshot,
                crate::HirSpecTermId,
                HirTypeId,
            >|
             -> Result<_, FrontendFailure> {
                Ok(crate::SpecMemoryRange {
                    pointer: snapshot(r.pointer, false)?,
                    start_bytes: term(r.start_bytes),
                    end_bytes: term(r.end_bytes),
                    layout: memory.access(r.layout, span)?,
                })
            };
            A::Disjoint {
                left: range(left)?,
                right: range(right)?,
            }
        }
        A::Alive(pointer) => A::Alive(snapshot(*pointer, false)?),
        A::SameAllocation { left, right } => A::SameAllocation {
            left: snapshot(*left, false)?,
            right: snapshot(*right, false)?,
        },
        A::Initialized {
            pointer,
            start_bytes,
            end_bytes,
            layout,
        } => A::Initialized {
            pointer: snapshot(*pointer, false)?,
            start_bytes: term(*start_bytes),
            end_bytes: term(*end_bytes),
            layout: memory.access(*layout, span)?,
        },
        A::Pure(id) => A::Pure(term(*id)),
        A::Permission(c) => A::Permission(claim(c)?),
        A::PointsTo { memory, value } => A::PointsTo {
            memory: claim(memory)?,
            value: value.map(term),
        },
        A::Separation(ids) => A::Separation(ids.iter().copied().map(assertion).collect()),
        A::Exists {
            binder,
            body,
            witness,
        } => A::Exists {
            binder: VirSpecBinderId::new(binder.get()),
            body: assertion(*body),
            witness: witness.map(term),
        },
    })
}

fn lower_authority_snapshot(
    hir: &HirProgram,
    memory: &LoweredMemorySchema,
    snapshot: HirSpecSnapshot,
    span: ByteSpan,
) -> Result<VirSpecSnapshot, FrontendFailure> {
    let ty = match snapshot {
        HirSpecSnapshot::Local { function, local } => hir
            .function_by_id(function)
            .and_then(|f| f.body())
            .and_then(|b| b.locals.get(local.get() as usize))
            .map(|l| l.ty),
        HirSpecSnapshot::Result { function } => hir
            .function_by_id(function)
            .map(|f| f.signature.return_type),
        _ => None,
    }
    .ok_or_else(|| invalid_hir(span))?;
    let target = match hir.type_kind(ty) {
        Some(crate::HirTypeKind::Reference { pointee, .. }) => *pointee,
        _ => ty,
    };
    let offset = if matches!(
        hir.type_kind(target),
        Some(crate::HirTypeKind::Slice { .. })
    ) {
        2
    } else {
        1
    };
    // Validated sized Own/reference ABI is exactly [pointer, permission]. Raw
    // pointers cannot supply authority; HIR validation rejects that case.
    Ok(match lower_snapshot(hir, memory, snapshot, span)? {
        VirSpecSnapshot::Parameter { function, slot } => VirSpecSnapshot::Parameter {
            function,
            slot: slot.checked_add(offset).ok_or_else(|| invalid_hir(span))?,
        },
        VirSpecSnapshot::Result { function, slot } => VirSpecSnapshot::Result {
            function,
            slot: slot.checked_add(offset).ok_or_else(|| invalid_hir(span))?,
        },
        VirSpecSnapshot::Value { .. }
        | VirSpecSnapshot::EntryParameter { .. }
        | VirSpecSnapshot::Memory { .. } => {
            return Err(invalid_hir(span));
        }
    })
}

fn lower_snapshot(
    hir: &HirProgram,
    memory: &LoweredMemorySchema,
    snapshot: HirSpecSnapshot,
    span: ByteSpan,
) -> Result<VirSpecSnapshot, FrontendFailure> {
    Ok(match snapshot {
        HirSpecSnapshot::Length {
            function,
            parameter,
            entry,
        } => {
            let Some(parameter) = parameter else {
                return Ok(VirSpecSnapshot::Result {
                    function: VirFunctionId::new(function.get()),
                    slot: 1,
                });
            };
            let local = *hir
                .function_by_id(function)
                .and_then(|f| f.body())
                .and_then(|b| b.parameters.get(parameter as usize))
                .ok_or_else(|| invalid_hir(span))?;
            let slot = hir_parameter_abi_slot(hir, memory, function, local, span)?
                .checked_add(1)
                .ok_or_else(|| invalid_hir(span))?;
            let function = VirFunctionId::new(function.get());
            if entry {
                VirSpecSnapshot::EntryParameter { function, slot }
            } else {
                VirSpecSnapshot::Parameter { function, slot }
            }
        }
        HirSpecSnapshot::Memory {
            function,
            parameter,
            old,
            projection,
        } => VirSpecSnapshot::Memory {
            function: VirFunctionId::new(function.get()),
            parameter,
            old,
            projection: match projection {
                crate::SpecMemoryProjection::Cell => crate::SpecMemoryProjection::Cell,
                crate::SpecMemoryProjection::Field(field) => {
                    crate::SpecMemoryProjection::Field(memory.field(field, span)?)
                }
                crate::SpecMemoryProjection::Index(index) => {
                    crate::SpecMemoryProjection::Index(index)
                }
            },
        },
        HirSpecSnapshot::EntryParameter {
            function,
            parameter,
        } => {
            let local = *hir
                .function_by_id(function)
                .and_then(|f| f.body())
                .and_then(|body| body.parameters.get(parameter as usize))
                .ok_or_else(|| invalid_hir(span))?;
            VirSpecSnapshot::EntryParameter {
                function: VirFunctionId::new(function.get()),
                slot: hir_parameter_abi_slot(hir, memory, function, local, span)?,
            }
        }
        HirSpecSnapshot::Local { function, local } => VirSpecSnapshot::Parameter {
            function: VirFunctionId::new(function.get()),
            slot: hir_parameter_abi_slot(hir, memory, function, local, span)?,
        },
        HirSpecSnapshot::Result { function } => VirSpecSnapshot::Result {
            function: VirFunctionId::new(function.get()),
            slot: 0,
        },
        HirSpecSnapshot::LoopEntry { .. } => return Err(invalid_hir(span)),
    })
}

fn lower_spec_location(
    location: HirSpecLocation,
    local_specs: &[super::local_spec::LocalSpec],
    loop_specs: &[super::loop_spec::LoopSpec],
) -> Option<VirSpecLocation> {
    match location {
        HirSpecLocation::Statement { function, prove } => local_specs
            .iter()
            .find(|s| s.prove == prove && s.function.get() == function.get())
            .map(super::local_spec::LocalSpec::location),
        HirSpecLocation::FunctionEntry { function } => Some(VirSpecLocation::FunctionEntry {
            function: VirFunctionId::new(function.get()),
        }),
        HirSpecLocation::FunctionResult { function } => Some(VirSpecLocation::FunctionResult {
            function: VirFunctionId::new(function.get()),
        }),
        HirSpecLocation::LoopHead { function, loop_id } => loop_specs
            .iter()
            .find(|s| s.function.get() == function.get() && s.loop_id == loop_id)
            .map(|s| {
                VirSpecLocation::Runtime(VirLocation::BlockEntry {
                    function: s.function,
                    block: s.boundary.header,
                })
            }),
    }
}

fn lower_spec_term_kind(
    hir: &HirProgram,
    memory: &LoweredMemorySchema,
    kind: &HirSpecTermKind,
    source_span: ByteSpan,
) -> Result<VirSpecTermKind, FrontendFailure> {
    let term = |id: crate::frontend::hir::HirSpecTermId| VirSpecTermId::new(id.get());
    Ok(match kind {
        HirSpecTermKind::Bool(value) => VirSpecTermKind::Bool(*value),
        HirSpecTermKind::CheckedAdd { left, right } => VirSpecTermKind::CheckedAdd {
            left: term(*left),
            right: term(*right),
        },
        HirSpecTermKind::CheckedSub { left, right } => VirSpecTermKind::CheckedSub {
            left: term(*left),
            right: term(*right),
        },
        HirSpecTermKind::CheckedScale { operand, stride } => VirSpecTermKind::CheckedScale {
            operand: term(*operand),
            stride: *stride,
        },
        HirSpecTermKind::RangeContains {
            outer_start,
            outer_end,
            inner_start,
            inner_end,
        } => VirSpecTermKind::RangeContains {
            outer_start: term(*outer_start),
            outer_end: term(*outer_end),
            inner_start: term(*inner_start),
            inner_end: term(*inner_end),
        },
        HirSpecTermKind::RangeDisjoint {
            left_start,
            left_end,
            right_start,
            right_end,
        } => VirSpecTermKind::RangeDisjoint {
            left_start: term(*left_start),
            left_end: term(*left_end),
            right_start: term(*right_start),
            right_end: term(*right_end),
        },
        HirSpecTermKind::U64(value) => VirSpecTermKind::U64(*value),
        HirSpecTermKind::Binder(binder) => {
            VirSpecTermKind::Binder(VirSpecBinderId::new(binder.get()))
        }
        HirSpecTermKind::Snapshot(snapshot) => {
            VirSpecTermKind::Snapshot(lower_snapshot(hir, memory, *snapshot, source_span)?)
        }
        HirSpecTermKind::Equal { left, right } => VirSpecTermKind::Equal {
            left: term(*left),
            right: term(*right),
        },
        HirSpecTermKind::LessThan { left, right } => VirSpecTermKind::LessThan {
            left: term(*left),
            right: term(*right),
        },
        HirSpecTermKind::LessOrEqual { left, right } => VirSpecTermKind::LessOrEqual {
            left: term(*left),
            right: term(*right),
        },
        HirSpecTermKind::Not(operand) => VirSpecTermKind::Not(term(*operand)),
        HirSpecTermKind::And(operands) => {
            VirSpecTermKind::And(operands.iter().copied().map(term).collect())
        }
        HirSpecTermKind::Or(operands) => {
            VirSpecTermKind::Or(operands.iter().copied().map(term).collect())
        }
    })
}
