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
    lower_hir_specs(hir, memory, source_map, &mut specs)?;
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
) -> Result<(), FrontendFailure> {
    let clause_base =
        u32::try_from(specs.clauses().len()).map_err(|_| invalid_hir(hir.entry_function().span))?;

    for predicate in hir.predicates() {
        let origin = spec_source_origin(source_map, predicate.span)
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
        let origin =
            spec_source_origin(source_map, binder.span).ok_or_else(|| invalid_hir(binder.span))?;
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
        let origin =
            spec_source_origin(source_map, term.span).ok_or_else(|| invalid_hir(term.span))?;
        specs.terms_mut().push(VirSpecTerm {
            id: VirSpecTermId::new(term.id.get()),
            clause: shifted_clause_id(clause_base, term.clause)
                .ok_or_else(|| invalid_hir(term.span))?,
            ty: lower_spec_type(hir, term.ty).ok_or_else(|| invalid_hir(term.span))?,
            kind: lower_spec_term_kind(hir, memory, &term.kind, term.span)?,
            origin,
        });
    }

    for clause in &hir.specs().clauses {
        let origin =
            spec_source_origin(source_map, clause.span).ok_or_else(|| invalid_hir(clause.span))?;
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
            location: lower_spec_location(clause.location)
                .ok_or_else(|| invalid_hir(clause.span))?,
            origin: VirSpecClauseOrigin::Explicit { origin },
            kind: VirSpecClauseKind::Logic {
                root: VirSpecTermId::new(clause.root.get()),
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
        let origin =
            spec_source_origin(source_map, prove.span).ok_or_else(|| invalid_hir(prove.span))?;
        specs.proves_mut().push(VirSpecProve {
            id: VirSpecProveId::new(prove.id.get()),
            function: VirFunctionId::new(prove.function.get()),
            location: lower_spec_location(prove.location).ok_or_else(|| invalid_hir(prove.span))?,
            clause: shifted_clause_id(clause_base, prove.clause)
                .ok_or_else(|| invalid_hir(prove.span))?,
            origin,
        });
    }
    for entry in &hir.specs().trust_entries {
        let origin =
            spec_source_origin(source_map, entry.span).ok_or_else(|| invalid_hir(entry.span))?;
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

pub(super) fn spec_source_spans(hir: &HirProgram) -> Vec<ByteSpan> {
    hir.predicates()
        .iter()
        .map(|predicate| predicate.span)
        .chain(hir.specs().binders.iter().map(|binder| binder.span))
        .chain(hir.specs().terms.iter().map(|term| term.span))
        .chain(hir.specs().clauses.iter().map(|clause| clause.span))
        .chain(hir.specs().proves.iter().map(|prove| prove.span))
        .chain(hir.specs().trust_entries.iter().map(|entry| entry.span))
        .chain(
            hir.specs()
                .loop_invariants
                .iter()
                .map(|invariant| invariant.span),
        )
        .collect()
}

fn spec_source_origin(source_map: &VirSourceMap, span: ByteSpan) -> Option<crate::VirOriginId> {
    source_map.user_origin(VirSourceId::new(0), span)
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
        _ => None,
    }
}

fn lower_spec_location(location: HirSpecLocation) -> Option<VirSpecLocation> {
    match location {
        HirSpecLocation::FunctionEntry { function } => Some(VirSpecLocation::FunctionEntry {
            function: VirFunctionId::new(function.get()),
        }),
        HirSpecLocation::FunctionResult { function } => Some(VirSpecLocation::FunctionResult {
            function: VirFunctionId::new(function.get()),
        }),
        HirSpecLocation::LoopHead { .. } => None,
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
        HirSpecTermKind::U64(value) => VirSpecTermKind::U64(*value),
        HirSpecTermKind::Binder(binder) => {
            VirSpecTermKind::Binder(VirSpecBinderId::new(binder.get()))
        }
        HirSpecTermKind::Snapshot(snapshot) => VirSpecTermKind::Snapshot(match snapshot {
            HirSpecSnapshot::Local { function, local } => VirSpecSnapshot::Parameter {
                function: VirFunctionId::new(function.get()),
                slot: hir_parameter_abi_slot(hir, memory, *function, *local, source_span)?,
            },
            HirSpecSnapshot::Result { function } => VirSpecSnapshot::Result {
                function: VirFunctionId::new(function.get()),
                slot: 0,
            },
        }),
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
