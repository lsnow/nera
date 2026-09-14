//! Deterministic, fail-closed lowering from concrete typed HIR to VIR v0.

use std::collections::{BTreeMap, BTreeSet};

mod abi;
mod contract;
#[cfg(test)]
mod tests;

mod aggregate;
mod assignment;
mod call;
mod cfg;
mod cleanup;
mod concrete;
mod draft;
mod liveness;
mod loan_end;
mod local_spec;
mod memory;
mod place;
mod post_cfg;
mod refill;
mod unit;

use super::FrontendFailure;
use super::hir::visit::{HirVisitor, walk_expression, walk_statement};
use super::hir::{
    HirBlock, HirBoundsSource, HirCall, HirCallingConvention, HirExpression, HirExpressionKind,
    HirForSource, HirFunction, HirIntegerPredicate, HirLocal, HirLocalId, HirLoopId, HirMatchArm,
    HirPattern, HirPatternKind, HirPlace, HirPlaceAccess, HirPlaceBase, HirProgram,
    HirProjectionKind, HirRegionOrigin, HirScopeId, HirSpecBinderOwner, HirSpecClauseOwner,
    HirSpecContractPosition, HirSpecLocation, HirSpecSnapshot, HirSpecTermKind, HirStatement,
    HirStatementKind, HirTrustPolicyKind, HirTrustScope, HirTypeId, HirTypeKind, HirUseMode,
    ResolvedHirPlace, ResolvedHirProjection, ResolvedHirProjectionKind,
};
use crate::vir::{
    RuntimeVirProgram, ValidatedVirUnit, VirAbiSignature, VirAbiValue, VirBorrowEnvironment,
    VirBorrowRegion, VirBorrowRegionConstraint, VirBorrowRegionConstraintId, VirBorrowRegionId,
    VirBorrowRegionOrigin, VirBorrowRegionScope, VirCallTarget, VirConstant, VirContractAccess,
    VirContractFree, VirContractId, VirContractInitialization, VirContractLiveness,
    VirContractOwnership, VirContractPermission, VirContractPointer, VirContractPosition,
    VirContractResourceSummary, VirFunctionId, VirGeneratedReason, VirIndexBounds, VirInstruction,
    VirIntegerPredicate, VirLoanEffect, VirLoanId, VirLoanKind, VirLoanRange, VirLocation,
    VirMemoryTypeKind, VirOriginId, VirPredicate, VirPredicateId, VirRegionId, VirSourceId,
    VirSourceMap, VirSpecBinder, VirSpecBinderId, VirSpecBinderOwner, VirSpecClause,
    VirSpecClauseId, VirSpecClauseKind, VirSpecClauseOrigin, VirSpecClauseOwner,
    VirSpecEnvironment, VirSpecLocation, VirSpecProve, VirSpecProveId, VirSpecSnapshot,
    VirSpecTerm, VirSpecTermId, VirSpecTermKind, VirSpecType, VirTerminator, VirTrustEntry,
    VirTrustEntryId, VirTrustPolicyKind, VirTrustScope, VirType, VirUnit, VirUnitVersion, VirValue,
    VirValueId,
};
use crate::{ByteSpan, SourceFile};
use aggregate::ObjectTemporaryStorage;
use call::{AbiCallStorage, AbiCallStorageRole};
use cfg::{
    CfgBuilder, DeferredLoanEnd, EnvironmentBlock, LocalEnvironment, LoweredLoan,
    LoweredLoanMetadata, LoweredValue,
};
use cleanup::ScopeExitPlan;
use concrete::ConcreteTypes;
use draft::{
    DraftObjectIdentity, DraftRegionConstraint, DraftSourceIdentity, PendingAssignmentSource,
    PendingCleanupKind,
};
use liveness::{
    LoopLiveness, block_live_in, for_loop_liveness, loop_liveness, match_arm_live_in,
    statement_live_outs,
};
use memory::LoweredMemorySchema;
use place::{LoweredAddress, LoweredObject, LoweredPlace};
use unit::DraftLoweredFunction;

use abi::{
    abi_result, assign_abi_slots, classify_hir_signature, hir_parameter_abi_slot,
    require_pointer_abi_authority,
};
use contract::{infer_contracts, spec_source_spans};

const CORE0_REGION: VirRegionId = VirRegionId::new(0);

pub(super) fn lower(
    hir: &HirProgram,
    source: &SourceFile,
) -> Result<ValidatedVirUnit, FrontendFailure> {
    lower_sources(hir, &[source], false)
}

pub(super) fn lower_modules(
    hir: &HirProgram,
    sources: &[&SourceFile],
) -> Result<ValidatedVirUnit, FrontendFailure> {
    lower_sources(hir, sources, true)
}

fn lower_sources(
    hir: &HirProgram,
    sources: &[&SourceFile],
    modules: bool,
) -> Result<ValidatedVirUnit, FrontendFailure> {
    hir.validate_tables()
        .map_err(|_| invalid_hir(hir.entry_function().span))?;
    if (!modules && hir.modules().len() != 1)
        || hir.entry_function().module != hir.entry_module_id()
        || !hir.entry_function().generic_parameters.is_empty()
    {
        return Err(invalid_hir(hir.entry_function().span));
    }
    let memory = LoweredMemorySchema::build(hir, hir.entry_function().span)?;
    let mut draft_functions = Vec::new();
    for function in hir
        .functions()
        .iter()
        .filter(|function| function.generic_parameters.is_empty())
    {
        if function.signature.calling_convention != HirCallingConvention::Nera
            || function.body().is_none()
        {
            return Err(invalid_hir(function.span));
        }
        let lowered = (|| Lowerer::new(hir, function, memory.clone())?.lower_function())()
            .map_err(|mut failure: FrontendFailure| {
                failure.source = Some(crate::VirSourceId::new(function.module.get()));
                failure
            })?;
        draft_functions.push(lowered);
    }
    // No raw VirUnit exists until every function has completed the same fixed
    // post-CFG pass sequence. Any failure drops the complete private draft.
    let lowered_functions = draft_functions
        .into_iter()
        .map(|draft| post_cfg::canonicalize_function(memory.schema(), draft))
        .collect::<Result<Vec<_>, _>>()?;
    let mut functions = Vec::with_capacity(lowered_functions.len());
    let mut function_abis = Vec::with_capacity(lowered_functions.len());
    let mut source_map_entries = Vec::new();
    let mut local_specs = Vec::new();
    for lowered in lowered_functions {
        local_specs.extend(lowered.local_specs);
        functions.push(lowered.function);
        function_abis.push(lowered.abi);
        source_map_entries.extend(lowered.source_map_entries);
    }
    let source_span = hir.entry_function().span;
    let abis = crate::vir::VirAbiEnvironment {
        functions: function_abis,
    };
    let mut runtime = RuntimeVirProgram {
        semantic_profile: crate::VIR_SYSTEM_SEMANTICS_V2,
        entry: VirFunctionId::new(hir.entry_function_id().get()),
        functions,
        abis,
    };
    let mut spec_sources = std::collections::BTreeMap::new();
    let source_map = if modules {
        let mut files = Vec::new();
        let used: std::collections::BTreeSet<_> = hir
            .functions()
            .iter()
            .map(|f| f.module)
            .chain(hir.predicates().iter().map(|p| p.module))
            .collect();
        for module in used {
            let source = sources
                .get(module.index())
                .ok_or_else(|| invalid_hir(source_span))?;
            spec_sources.insert(module, crate::VirSourceId::new(files.len() as u32));
            let entries = source_map_entries
                .iter()
                .copied()
                .filter(|entry| {
                    hir.function_by_id(crate::HirFunctionId::new(entry.location().function().get()))
                        .is_some_and(|f| f.module == module)
                })
                .collect();
            files.push((
                crate::VirSource {
                    id: crate::VirSourceId::new(files.len() as u32),
                    name: source.path().to_string_lossy().into_owned(),
                    byte_len: source.len(),
                },
                entries,
                spec_source_spans(hir, module),
            ));
        }
        VirSourceMap::from_module_lowering(files)
    } else {
        spec_sources.insert(crate::HirModuleId::new(0), crate::VirSourceId::new(0));
        VirSourceMap::from_lowering(
            sources[0].path().to_string_lossy(),
            sources[0].len(),
            source_map_entries,
            spec_source_spans(hir, crate::HirModuleId::new(0)),
        )
    };
    patch_lowered_loan_origins(&mut runtime, &source_map)?;
    let borrows = lower_borrow_environment(hir, &runtime, &source_map)?;
    let specs = infer_contracts(
        hir,
        &memory,
        &runtime,
        &source_map,
        &local_specs,
        &spec_sources,
    )?;
    VirUnit {
        version: VirUnitVersion::V25,
        memory: memory.into_schema(),
        borrows,
        runtime,
        specs,
        source_map,
    }
    .into_validated()
    .map_err(|_| invalid_hir(source_span))
}

fn function_symbol(hir: &HirProgram, function: &HirFunction) -> String {
    let path = &hir.modules()[function.module.index()].path;
    if hir.modules().len() == 1 && *path == super::hir::HirModulePath::root() {
        function.name.clone()
    } else {
        format!("{}::{}", path.segments().join("::"), function.name)
    }
}

fn patch_lowered_loan_origins(
    runtime: &mut RuntimeVirProgram,
    source_map: &VirSourceMap,
) -> Result<(), FrontendFailure> {
    for function in &mut runtime.functions {
        for block in &mut function.blocks {
            for (ordinal, instruction) in block.instructions.iter_mut().enumerate() {
                let origin = match &mut instruction.instruction {
                    VirInstruction::LoanBegin { effect, .. }
                    | VirInstruction::LoanAliasShared { effect, .. }
                    | VirInstruction::LoanReborrow { effect, .. }
                    | VirInstruction::LoanEnd { effect } => &mut effect.origin,
                    VirInstruction::LoanAliasAuthority { effect, .. }
                    | VirInstruction::LoanReborrowAuthority { effect, .. }
                    | VirInstruction::LoanEndAuthority { effect } => &mut effect.origin,
                    _ => continue,
                };
                let location = VirLocation::Instruction {
                    function: function.id,
                    block: block.id,
                    ordinal: u64::try_from(ordinal)
                        .map_err(|_| invalid_hir(instruction.source_span))?,
                };
                *origin = source_map
                    .origin_at(location)
                    .filter(|origin| {
                        matches!(
                            origin.kind,
                            crate::VirOriginKind::Generated {
                                reason: VirGeneratedReason::LoanEffect,
                                ..
                            }
                        )
                    })
                    .map(|origin| origin.id)
                    .ok_or_else(|| invalid_hir(instruction.source_span))?;
            }
        }
    }
    Ok(())
}

fn lower_borrow_environment(
    hir: &HirProgram,
    runtime: &RuntimeVirProgram,
    source_map: &VirSourceMap,
) -> Result<VirBorrowEnvironment, FrontendFailure> {
    let mut regions = Vec::with_capacity(hir.regions().len());
    for region in hir.regions() {
        let super::hir::HirRegionOwner::Function(hir_owner) = region.owner else {
            if matches!(region.origin, HirRegionOrigin::AggregateErased) {
                continue;
            }
            return Err(invalid_hir(region.span));
        };
        let owner = VirFunctionId::new(hir_owner.get());
        let vir_region =
            vir_borrow_region_id(hir, region.id).ok_or_else(|| invalid_hir(region.span))?;
        let function = runtime
            .functions
            .iter()
            .find(|function| function.id == owner)
            .ok_or_else(|| invalid_hir(region.span))?;
        let mut blocks = Vec::new();
        let mut source_origin = None;
        for block in &function.blocks {
            for (ordinal, instruction) in block.instructions.iter().enumerate() {
                if matches!(region.origin, HirRegionOrigin::Inferred { .. })
                    && instruction.source_span == region.span
                    && matches!(instruction.instruction, VirInstruction::Call { .. })
                {
                    if blocks.last() != Some(&block.id) {
                        blocks.push(block.id);
                    }
                    source_origin.get_or_insert_with(|| {
                        source_map
                            .origin_at(VirLocation::Instruction {
                                function: owner,
                                block: block.id,
                                ordinal: ordinal as u64,
                            })
                            .map(|origin| origin.id)
                            .unwrap_or(VirOriginId::new(u32::MAX))
                    });
                }
                if let VirInstruction::LoanReborrowAuthority { region, effect, .. } =
                    &instruction.instruction
                {
                    if *region == vir_region {
                        if blocks.last() != Some(&block.id) {
                            blocks.push(block.id);
                        }
                        source_origin.get_or_insert(effect.origin);
                    }
                    continue;
                }
                let effect = match &instruction.instruction {
                    VirInstruction::LoanBegin { effect, .. }
                    | VirInstruction::LoanAliasShared { effect, .. }
                    | VirInstruction::LoanReborrow { effect, .. }
                    | VirInstruction::LoanEnd { effect } => effect,
                    _ => continue,
                };
                if effect.region == vir_region {
                    if blocks.last() != Some(&block.id) {
                        blocks.push(block.id);
                    }
                    if matches!(
                        instruction.instruction,
                        VirInstruction::LoanBegin { .. } | VirInstruction::LoanReborrow { .. }
                    ) {
                        source_origin.get_or_insert(effect.origin);
                    }
                }
            }
        }
        let signature_index = match region.origin {
            HirRegionOrigin::Parameter { index } => Some(index),
            _ => None,
        };
        let signature_region =
            signature_index.is_some() || region.origin == HirRegionOrigin::Result;
        let source_origin = if signature_region {
            source_map
                .origin_at(VirLocation::FunctionEntry { function: owner })
                .map(|origin| origin.id)
        } else {
            source_origin
        }
        .ok_or_else(|| invalid_hir(region.span))?;
        regions.push(VirBorrowRegion {
            id: vir_region,
            owner,
            origin: match region.origin {
                HirRegionOrigin::Parameter { index } => VirBorrowRegionOrigin::Parameter { index },
                HirRegionOrigin::Result => VirBorrowRegionOrigin::Result { index: 0 },
                HirRegionOrigin::LexicalScope { .. } => VirBorrowRegionOrigin::Lexical,
                HirRegionOrigin::Inferred { .. } => VirBorrowRegionOrigin::Inferred,
                HirRegionOrigin::AggregateErased => return Err(invalid_hir(region.span)),
            },
            scope: if signature_region {
                VirBorrowRegionScope::Function
            } else {
                VirBorrowRegionScope::Blocks(blocks)
            },
            source_origin,
        });
    }
    let constraints = hir
        .region_constraints()
        .iter()
        .map(|constraint| {
            let subregion = vir_borrow_region_id(hir, constraint.subregion)
                .ok_or_else(|| invalid_hir(constraint.span))?;
            let source_origin = regions
                .get(subregion.get() as usize)
                .filter(|region| region.id == subregion)
                .map(|region| region.source_origin)
                .ok_or_else(|| invalid_hir(constraint.span))?;
            Ok(VirBorrowRegionConstraint {
                id: VirBorrowRegionConstraintId::new(constraint.id.get()),
                owner: VirFunctionId::new(constraint.owner.get()),
                subregion,
                superregion: vir_borrow_region_id(hir, constraint.superregion)
                    .ok_or_else(|| invalid_hir(constraint.span))?,
                source_origin,
            })
        })
        .collect::<Result<Vec<_>, FrontendFailure>>()?;
    Ok(VirBorrowEnvironment::from_tables(regions, constraints))
}

fn vir_borrow_region_id(
    hir: &HirProgram,
    target: super::hir::HirRegionId,
) -> Option<VirBorrowRegionId> {
    hir.regions()
        .iter()
        .filter(|region| {
            matches!(
                (region.owner, region.origin),
                (
                    super::hir::HirRegionOwner::Function(_),
                    HirRegionOrigin::Inferred { .. }
                        | HirRegionOrigin::Parameter { .. }
                        | HirRegionOrigin::Result
                )
            )
        })
        .position(|region| region.id == target)
        .and_then(|index| u32::try_from(index).ok())
        .map(VirBorrowRegionId::new)
}

struct LoweredCondition {
    value: LoweredValue,
    fact_values: Vec<VirValue>,
}

#[derive(Clone)]
struct LoweredLoop {
    liveness: LoopLiveness,
    parent_scope: HirScopeId,
    continue_target: EnvironmentBlock,
    exit: EnvironmentBlock,
}

struct Lowerer<'hir> {
    local_specs: Vec<local_spec::LocalSpec>,
    hir: &'hir HirProgram,
    function: &'hir HirFunction,
    types: ConcreteTypes<'hir>,
    cfg: CfgBuilder,
    environment: LocalEnvironment,
    flow_facts: Vec<VirValue>,
    active_scopes: Vec<HirScopeId>,
    active_loops: Vec<LoweredLoop>,
    local_types: Vec<VirType>,
    storage_locals: BTreeSet<HirLocalId>,
    object_temporaries: Vec<ObjectTemporaryStorage>,
    abi_call_storage: Vec<AbiCallStorage>,
    abi: VirAbiSignature,
    abi_parameter_restores: Vec<(u32, HirLocalId)>,
    abi_indirect_result: Option<HirLocalId>,
    memory: LoweredMemorySchema,
    known_drop_flags: BTreeMap<VirValueId, bool>,
    next_loan: u32,
}

impl<'hir> Lowerer<'hir> {
    fn new(
        hir: &'hir HirProgram,
        function: &'hir HirFunction,
        memory: LoweredMemorySchema,
    ) -> Result<Self, FrontendFailure> {
        let body = function.body().ok_or_else(|| invalid_hir(function.span))?;
        let types = ConcreteTypes::new(hir);
        if !function.generic_parameters.is_empty()
            || function.signature.calling_convention != HirCallingConvention::Nera
            || body.parameters.len() != function.signature.parameters.len()
        {
            return Err(invalid_hir(function.span));
        }

        let abi = classify_hir_signature(types, &memory, &function.signature, function.span)?;

        let mut constructors = Vec::new();
        collect_constructors_in_block(&body.root, &mut constructors);
        refill::collect_assignment_sources(hir, &body.root, &mut constructors);
        let mut calls = Vec::new();
        collect_calls_in_block(&body.root, &mut calls);
        let mut addressable_storage_locals = collect_addressable_storage_locals(&body.root);
        addressable_storage_locals.retain(|local| {
            body.locals
                .get(local.index())
                .filter(|candidate| candidate.id == *local)
                .is_none_or(|candidate| slice_view_type(hir, candidate.ty).is_none())
        });
        let mut call_storage_specs = Vec::new();
        for expression in calls {
            let HirExpressionKind::Call(call) = &expression.kind else {
                return Err(invalid_hir(expression.span));
            };
            let call_abi = classify_hir_signature(
                types,
                &memory,
                &call.instantiated_signature,
                expression.span,
            )?;
            for (index, binding) in call_abi.parameters().iter().enumerate() {
                if binding.interface().storage == crate::VirInterfaceStorage::Indirect
                    && let VirAbiValue::IndirectAggregate { access } = binding.value()
                {
                    call_storage_specs.push((
                        expression,
                        AbiCallStorageRole::Argument(index),
                        *access,
                    ));
                }
            }
            if let Some(binding) = call_abi.results().first()
                && matches!(
                    binding.interface().storage,
                    crate::VirInterfaceStorage::Direct | crate::VirInterfaceStorage::Indirect
                )
                && let VirAbiValue::DirectAggregate { access, .. }
                | VirAbiValue::IndirectAggregate { access } = binding.value()
            {
                call_storage_specs.push((expression, AbiCallStorageRole::Result, *access));
            }
        }
        let has_indirect_result = abi
            .results()
            .first()
            .is_some_and(|binding| binding.value().is_indirect_aggregate());
        let total_locals = body
            .locals
            .len()
            .checked_add(constructors.len())
            .and_then(|count| count.checked_add(call_storage_specs.len()))
            .and_then(|count| count.checked_add(usize::from(has_indirect_result)))
            .ok_or_else(|| invalid_hir(function.span))?;
        let mut local_types = vec![None; total_locals];
        let mut storage_locals = BTreeSet::new();
        for local in &body.locals {
            let Some(slot) = local_types.get_mut(local.id.index()) else {
                return Err(invalid_hir(local.declaration_span));
            };
            let aggregate = types
                .aggregate_access(&memory, local.ty, local.declaration_span)?
                .is_some();
            let needs_storage = aggregate || addressable_storage_locals.contains(&local.id);
            let local_type = if needs_storage {
                VirType::Pointer {
                    access: memory.access(local.ty, local.declaration_span)?,
                }
            } else {
                types.local_type(&memory, local.ty, local.declaration_span)?
            };
            if needs_storage {
                storage_locals.insert(local.id);
            }
            if slot.replace(local_type).is_some() {
                return Err(invalid_hir(local.declaration_span));
            }
        }
        let mut object_temporaries = Vec::with_capacity(constructors.len());
        for (index, expression) in constructors.iter().enumerate() {
            let raw = body
                .locals
                .len()
                .checked_add(index)
                .and_then(|index| u32::try_from(index).ok())
                .ok_or_else(|| invalid_hir(expression.span))?;
            let local = HirLocalId::new(raw);
            let access = types
                .aggregate_access(&memory, expression.ty, expression.span)?
                .ok_or_else(|| invalid_hir(expression.span))?;
            local_types[local.index()] = Some(VirType::Pointer { access });
            object_temporaries.push(ObjectTemporaryStorage {
                owner: expression.id,
                ty: expression.ty,
                span: expression.span,
                local,
            });
        }
        let mut abi_call_storage = Vec::with_capacity(call_storage_specs.len());
        for (index, (expression, role, access)) in call_storage_specs.into_iter().enumerate() {
            let raw = body
                .locals
                .len()
                .checked_add(constructors.len())
                .and_then(|base| base.checked_add(index))
                .and_then(|index| u32::try_from(index).ok())
                .ok_or_else(|| invalid_hir(expression.span))?;
            let local = HirLocalId::new(raw);
            local_types[local.index()] = Some(VirType::Pointer { access });
            storage_locals.insert(local);
            abi_call_storage.push(AbiCallStorage {
                owner: expression.id,
                role,
                span: expression.span,
                local,
            });
        }
        let abi_indirect_result = if has_indirect_result {
            let raw = body
                .locals
                .len()
                .checked_add(constructors.len())
                .and_then(|base| base.checked_add(abi_call_storage.len()))
                .and_then(|index| u32::try_from(index).ok())
                .ok_or_else(|| invalid_hir(function.span))?;
            let local = HirLocalId::new(raw);
            let access = abi
                .results()
                .first()
                .and_then(|binding| binding.value().access())
                .ok_or_else(|| invalid_hir(function.span))?;
            local_types[local.index()] = Some(VirType::Pointer { access });
            storage_locals.insert(local);
            Some(local)
        } else {
            None
        };
        let local_types = local_types
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| invalid_hir(function.span))?;
        let (cfg, entry_environment, physical_parameters) = CfgBuilder::new_with_abi_parameters(
            VirFunctionId::new(function.id.get()),
            body.root.scope,
            total_locals,
            &abi.physical().parameters,
            function.span,
        )?;
        if entry_environment.scope() != body.root.scope {
            return Err(invalid_hir(function.span));
        }
        let mut lowerer = Self {
            local_specs: Vec::new(),
            hir,
            function,
            types,
            cfg,
            environment: entry_environment.entry_environment(),
            flow_facts: Vec::new(),
            active_scopes: vec![body.root.scope],
            active_loops: Vec::new(),
            local_types,
            storage_locals,
            object_temporaries,
            abi_call_storage,
            abi,
            abi_parameter_restores: Vec::new(),
            abi_indirect_result,
            memory,
            known_drop_flags: BTreeMap::new(),
            next_loan: 0,
        };
        lowerer.plan_aggregate_storage(body)?;
        lowerer.bind_abi_entry_parameters(body, &physical_parameters)?;
        Ok(lowerer)
    }

    fn plan_aggregate_storage(
        &mut self,
        body: &super::hir::HirBody,
    ) -> Result<(), FrontendFailure> {
        let mut planned = Vec::new();
        for local in &body.locals {
            if !self.storage_locals.contains(&local.id) {
                continue;
            }
            let indirect_parameter = body
                .parameters
                .iter()
                .position(|candidate| *candidate == local.id)
                .and_then(|index| self.abi.parameters().get(index))
                .is_some_and(|binding| binding.value().is_indirect_aggregate());
            if indirect_parameter {
                continue;
            }
            let access = self.memory.access(local.ty, local.declaration_span)?;
            let storage = self.emit_local_storage(access, local.declaration_span)?;
            planned.push((local.id, storage, Some(local.ty), local.declaration_span));
        }

        let constructors = self.object_temporaries.clone();
        for constructor in constructors {
            let span = constructor.span;
            let ty = constructor.ty;
            let access = self
                .types
                .aggregate_access(&self.memory, ty, span)?
                .ok_or_else(|| invalid_hir(span))?;
            let storage = self.emit_temporary_storage(access, span)?;
            planned.push((constructor.local, storage, Some(ty), span));
        }
        let call_storages = self.abi_call_storage.clone();
        for call_storage in call_storages {
            let VirType::Pointer { access } = self.local_types[call_storage.local.index()] else {
                return Err(invalid_hir(call_storage.span));
            };
            let storage = self.emit_temporary_storage(access, call_storage.span)?;
            planned.push((call_storage.local, storage, None, call_storage.span));
        }

        // `LocalStorage` is a strict entry-block prefix. Drop-flag constants
        // are therefore materialized only after every frame object exists.
        for (local, storage, hir_type, span) in planned {
            let drop_flag = match hir_type {
                Some(ty) => self.initial_drop_flag(ty, false, span)?,
                None => self.initial_access_drop_flag(storage.access, false, span)?,
            };
            self.environment.initialize(
                local,
                LoweredValue {
                    value: storage.pointer,
                    ty: VirType::Pointer {
                        access: storage.access,
                    },
                    metadata: None,
                    permission: Some(storage.permission),
                    drop_flag,
                    loan: None,
                },
                span,
            )?;
        }
        Ok(())
    }

    fn cleanup_object_temporary(
        &mut self,
        object: LoweredObject,
        source: DraftSourceIdentity,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if self.is_object_temporary(object, source_span)? {
            let identity = DraftObjectIdentity {
                pointer: object.pointer,
                permission: object.permission,
                access: object.access,
            };
            if let Some(condition) = object.drop_flag
                && self.known_drop_flags.get(&condition) != Some(&false)
            {
                self.cfg.emit_cleanup(
                    PendingCleanupKind::Object {
                        condition: Some(condition),
                    },
                    identity,
                    source,
                    source_span,
                )?;
                self.set_object_drop_flag(object, false, source_span)?;
            } else {
                self.cfg.emit_cleanup(
                    PendingCleanupKind::Object { condition: None },
                    identity,
                    source,
                    source_span,
                )?;
            }
        }
        Ok(())
    }

    fn emit_local_storage(
        &mut self,
        access: crate::VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<LoweredObject, FrontendFailure> {
        let pointer = self.fresh_value(VirType::Pointer { access }, source_span)?;
        let permission = self.fresh_value(VirType::Permission, source_span)?;
        self.emit(
            VirInstruction::LocalStorage {
                pointer_result: pointer,
                permission_result: permission,
                access,
            },
            source_span,
        )?;
        Ok(LoweredObject {
            pointer: pointer.id,
            permission: permission.id,
            access,
            drop_flag: None,
        })
    }

    fn emit_temporary_storage(
        &mut self,
        access: crate::VirMemoryAccess,
        parent_span: ByteSpan,
    ) -> Result<LoweredObject, FrontendFailure> {
        let pointer = self.fresh_value(VirType::Pointer { access }, parent_span)?;
        let permission = self.fresh_value(VirType::Permission, parent_span)?;
        self.emit_generated(
            VirInstruction::LocalStorage {
                pointer_result: pointer,
                permission_result: permission,
                access,
            },
            parent_span,
            VirGeneratedReason::TemporaryStorage,
        )?;
        Ok(LoweredObject {
            pointer: pointer.id,
            permission: permission.id,
            access,
            drop_flag: None,
        })
    }

    fn lower_function(mut self) -> Result<DraftLoweredFunction, FrontendFailure> {
        let function = self.function;
        let body = function.body().ok_or_else(|| invalid_hir(function.span))?;
        self.lower_block_statements(&body.root, &[])?;
        if self.cfg.has_open_block() {
            return Err(invalid_hir(function.span));
        }
        let abi = self.abi.clone();
        let entry_block = self.cfg.entry();
        let region_constraints = self
            .hir
            .region_constraints()
            .iter()
            .filter(|constraint| constraint.owner == function.id)
            .map(|constraint| {
                Ok(DraftRegionConstraint {
                    subregion: vir_borrow_region_id(self.hir, constraint.subregion)
                        .ok_or_else(|| invalid_hir(constraint.span))?,
                    superregion: vir_borrow_region_id(self.hir, constraint.superregion)
                        .ok_or_else(|| invalid_hir(constraint.span))?,
                })
            })
            .collect::<Result<Vec<_>, FrontendFailure>>()?;
        let body = self.cfg.finish_draft(function.span)?;
        Ok(DraftLoweredFunction {
            local_specs: self.local_specs,
            id: VirFunctionId::new(function.id.get()),
            name: function_symbol(self.hir, function),
            signature: abi.physical().clone(),
            contract: VirContractId::new(function.contract.get()),
            entry: entry_block,
            body,
            region_constraints,
            abi,
            source_span: function.span,
        })
    }

    fn lower_block_statements(
        &mut self,
        block: &HirBlock,
        live_after_block: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        let live_outs = statement_live_outs(block, live_after_block, &self.active_loop_liveness())?;
        for (statement, live_after) in block.statements.iter().zip(live_outs) {
            if !self.cfg.has_open_block() {
                return Err(invalid_hir(statement.span));
            }
            self.lower_statement(statement, block.span, &live_after)?;
            if self.cfg.has_open_block() {
                let parameters = &self
                    .function
                    .body()
                    .ok_or_else(|| invalid_hir(statement.span))?
                    .parameters;
                let ended = (0..self.environment.len())
                    .filter_map(|index| {
                        let local = HirLocalId::new(u32::try_from(index).ok()?);
                        self.environment
                            .optional(local)
                            .is_some_and(|value| {
                                matches!(value.loan, Some(LoweredLoan::ConditionalAuthority { .. }))
                            })
                            .then_some(local)
                    })
                    .filter(|local| !parameters.contains(local) && !live_after.contains(local))
                    .collect::<Vec<_>>();
                for local in ended {
                    self.emit_local_drop(local, statement.span)?;
                }
            }
        }
        Ok(())
    }

    fn lower_statement(
        &mut self,
        statement: &HirStatement,
        containing_block_span: ByteSpan,
        live_after: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        match &statement.kind {
            HirStatementKind::Prove { prove } => self.lower_local_prove(*prove, statement.span),
            HirStatementKind::Declare { local } => {
                let object = self.local_object(*local, statement.span)?;
                if self
                    .memory
                    .schema()
                    .object_shape(object.access)
                    .map_err(|_| invalid_hir(statement.span))?
                    .supports_resource_storage_reset()
                {
                    self.emit(
                        VirInstruction::ResourceStorageReset {
                            pointer: object.pointer,
                            permission: object.permission,
                            access: object.access,
                        },
                        statement.span,
                    )?;
                    // Armed means storage may hold payload, not whole-value
                    // completeness. ObjectDrop checks each actual leaf.
                    return self.set_object_drop_flag(object, true, statement.span);
                }
                self.emit(
                    VirInstruction::StorageReset {
                        pointer: object.pointer,
                        permission: object.permission,
                        access: object.access,
                    },
                    statement.span,
                )
            }
            HirStatementKind::Let { local, value } => {
                let local_type = self.local(*local, statement.span)?.ty;
                if local_type != value.ty {
                    return Err(invalid_hir(statement.span));
                }
                if self.storage_locals.contains(local) {
                    let destination = self.local_object(*local, statement.span)?;
                    if self
                        .types
                        .aggregate_access(&self.memory, local_type, statement.span)?
                        .is_some()
                    {
                        let source = self.lower_object_expression(value)?;
                        self.emit_object_assignment(
                            destination,
                            source,
                            object_source_mode(value)?,
                            DraftSourceIdentity::HirNode(statement.id),
                            statement.span,
                        )
                    } else {
                        let source = self.lower_expression(value)?;
                        if source.permission.is_some()
                            || source.loan.is_some()
                            || destination.access
                                != self.memory.access(local_type, statement.span)?
                        {
                            return Err(invalid_hir(statement.span));
                        }
                        self.cfg.emit_assignment(
                            destination.pointer,
                            destination.permission,
                            destination.access,
                            PendingAssignmentSource::Scalar {
                                value: source.value,
                            },
                            DraftSourceIdentity::HirNode(statement.id),
                            statement.span,
                        )
                    }
                } else {
                    let value = self.lower_expression(value)?;
                    self.assign_local(*local, value, statement.span)
                }
            }
            HirStatementKind::Assign { destination, value } => {
                self.lower_assign(destination, value, statement.span)
            }
            HirStatementKind::Free { pointer } => {
                let pointer_type = self.local(*pointer, statement.span)?.ty;
                let Some(HirTypeKind::Own { pointee }) = self.hir.type_kind(pointer_type) else {
                    return Err(invalid_hir(statement.span));
                };
                if self.types.require_pointer(pointer_type, statement.span)? != *pointee {
                    return Err(invalid_hir(statement.span));
                }
                let pointer_value = self.lookup_local(*pointer, statement.span)?;
                let permission = pointer_value
                    .permission
                    .ok_or_else(|| invalid_hir(statement.span))?;
                if !matches!(pointer_value.ty, VirType::Pointer { .. }) {
                    return Err(invalid_hir(statement.span));
                }
                self.emit_pointee_cleanup(*pointer, pointer_value, None, statement.span)?;
                self.emit(
                    VirInstruction::Free {
                        pointer: pointer_value.value,
                        permission,
                    },
                    statement.span,
                )?;
                self.set_local_drop_flag(*pointer, false, statement.span)?;
                Ok(())
            }
            HirStatementKind::Return { value } => self.lower_return(value.as_ref(), statement.span),
            HirStatementKind::Block { block } => {
                self.lower_nested_block(block, containing_block_span, live_after)
            }
            HirStatementKind::If {
                condition,
                then_block,
                else_block,
            } => self.lower_if(
                condition,
                then_block,
                else_block.as_ref(),
                statement.span,
                containing_block_span,
                live_after,
            ),
            HirStatementKind::While {
                loop_id,
                condition,
                body,
            } => self.lower_while(
                *loop_id,
                condition,
                body,
                statement.span,
                containing_block_span,
                live_after,
            ),
            HirStatementKind::Break { target } => {
                self.lower_loop_exit(*target, true, statement.span)
            }
            HirStatementKind::Continue { target } => {
                self.lower_loop_exit(*target, false, statement.span)
            }
            HirStatementKind::Evaluate { expression } => {
                let HirExpressionKind::Call(call) = &expression.kind else {
                    return Err(invalid_hir(statement.span));
                };
                if self
                    .lower_call(expression, call, expression.span)?
                    .is_some()
                {
                    return Err(invalid_hir(statement.span));
                }
                Ok(())
            }
            HirStatementKind::For {
                loop_id,
                pattern,
                source,
                body,
            } => self.lower_for(
                *loop_id,
                pattern,
                source,
                body,
                statement.span,
                containing_block_span,
                live_after,
            ),
            HirStatementKind::Match { scrutinee, arms } => self.lower_match(
                scrutinee,
                arms,
                statement.span,
                containing_block_span,
                live_after,
            ),
        }
    }

    fn lower_nested_block(
        &mut self,
        block: &HirBlock,
        containing_block_span: ByteSpan,
        live_after: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        let retained_scope = self
            .active_scopes
            .last()
            .copied()
            .ok_or_else(|| invalid_hir(block.span))?;
        self.enter_scope(block)?;
        self.lower_block_statements(block, live_after)?;
        if self.cfg.has_open_block() {
            self.emit_scope_exit_actions(Some(retained_scope), block.span)?;
        }
        self.leave_scope(block)?;
        // A loop/branch inside a lexical block can leave a continuation whose
        // source span is narrower than the surrounding scope. Resume outside
        // it with an explicit SSA edge, preserving the inner cleanup origins.
        if self.cfg.has_open_block() && !self.cfg.open_block_covers(containing_block_span) {
            let locals = self.visible_locals_needed(live_after, block.span)?;
            let types = self
                .flow_facts
                .iter()
                .map(|value| value.ty)
                .collect::<Vec<_>>();
            let continuation = self.cfg.create_environment_block_with_extras(
                retained_scope,
                &locals,
                &[&self.environment],
                &types,
                containing_block_span,
            )?;
            self.emit_drops_not_in_environment(&continuation, block.span)?;
            let target = continuation.target_from_with_extras(
                &self.environment,
                &self.flow_facts,
                block.span,
            )?;
            self.cfg.terminate_generated(
                VirTerminator::Jump { target },
                block.span,
                VirGeneratedReason::ControlFlowEdge,
            )?;
            self.cfg
                .switch_to(continuation.block(), containing_block_span)?;
            self.environment = continuation.entry_environment();
            self.flow_facts = continuation.extra_parameters().to_vec();
        }
        Ok(())
    }

    fn lower_if(
        &mut self,
        condition: &HirExpression,
        then_block: &HirBlock,
        else_block: Option<&HirBlock>,
        statement_span: ByteSpan,
        containing_block_span: ByteSpan,
        live_after: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        let lowered_condition = self.lower_condition(condition)?;
        if lowered_condition.value.ty != VirType::Bool
            || lowered_condition.value.permission.is_some()
        {
            return Err(invalid_hir(condition.span));
        }

        let parent_scope = self
            .active_scopes
            .last()
            .copied()
            .ok_or_else(|| invalid_hir(statement_span))?;
        let predecessor = self.environment.clone();
        let predecessor_facts = self.flow_facts.clone();
        let join_locals = self.visible_locals_needed(live_after, statement_span)?;
        let active_loop_liveness = self.active_loop_liveness();
        let then_live_in = block_live_in(then_block, live_after, &active_loop_liveness)?;
        let mut then_locals = self.visible_locals_needed(&then_live_in, statement_span)?;
        let else_live_in = match else_block {
            Some(block) => block_live_in(block, live_after, &active_loop_liveness)?,
            None => live_after.to_vec(),
        };
        let mut else_locals = self.visible_locals_needed(&else_live_in, statement_span)?;
        self.retain_conditional_drop_locals(&mut then_locals, &mut else_locals);
        let mut branch_facts = predecessor_facts.clone();
        extend_unique_facts(&mut branch_facts, &lowered_condition.fact_values);
        let branch_fact_types = branch_facts
            .iter()
            .map(|value| value.ty)
            .collect::<Vec<_>>();
        let then_target = self.cfg.create_environment_block_with_extras(
            then_block.scope,
            &then_locals,
            &[&predecessor],
            &branch_fact_types,
            then_block.span,
        )?;
        let else_target = self.cfg.create_environment_block_with_extras(
            else_block.map_or(parent_scope, |block| block.scope),
            &else_locals,
            &[&predecessor],
            &branch_fact_types,
            else_block.map_or(statement_span, |block| block.span),
        )?;
        let then_falls_through = block_falls_through(then_block);
        let else_falls_through = else_block.is_none_or(block_falls_through);
        let join_needed = then_falls_through || else_falls_through;
        let join_facts = if then_falls_through && else_falls_through {
            &predecessor_facts
        } else {
            &branch_facts
        };
        let join_fact_types = join_facts.iter().map(|value| value.ty).collect::<Vec<_>>();
        let join = join_needed
            .then(|| {
                self.cfg.create_environment_block_with_extras(
                    parent_scope,
                    &join_locals,
                    &[&predecessor],
                    &join_fact_types,
                    containing_block_span,
                )
            })
            .transpose()?;

        let then_edge =
            then_target.target_from_with_extras(&predecessor, &branch_facts, statement_span)?;
        let else_edge =
            else_target.target_from_with_extras(&predecessor, &branch_facts, statement_span)?;
        self.cfg.terminate(
            VirTerminator::Branch {
                condition: lowered_condition.value.value,
                then_target: then_edge,
                else_target: else_edge,
            },
            statement_span,
        )?;

        self.lower_branch_block(then_block, &then_target, join.as_ref(), live_after)?;
        if let Some(block) = else_block {
            self.lower_branch_block(block, &else_target, join.as_ref(), live_after)?;
        } else {
            self.lower_empty_branch(&else_target, join.as_ref(), statement_span)?;
        }

        if let Some(join) = join {
            self.cfg.switch_to(join.block(), statement_span)?;
            self.environment = join.entry_environment();
            self.flow_facts = join.extra_parameters().to_vec();
        } else {
            self.environment = predecessor;
            self.flow_facts = predecessor_facts;
        }
        Ok(())
    }

    fn lower_while(
        &mut self,
        loop_id: HirLoopId,
        condition: &HirExpression,
        body: &HirBlock,
        statement_span: ByteSpan,
        containing_block_span: ByteSpan,
        live_after: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        if self
            .active_loops
            .iter()
            .any(|active| active.liveness.loop_id == loop_id)
        {
            return Err(invalid_hir(statement_span));
        }
        let outer_liveness = self.active_loop_liveness();
        let liveness = loop_liveness(
            loop_id,
            condition,
            body,
            live_after,
            &outer_liveness,
            statement_span,
        )?;
        let parent_scope = self
            .active_scopes
            .last()
            .copied()
            .ok_or_else(|| invalid_hir(statement_span))?;
        let predecessor = self.environment.clone();
        let predecessor_facts = self.flow_facts.clone();
        let fact_types = predecessor_facts
            .iter()
            .map(|value| value.ty)
            .collect::<Vec<_>>();
        let header_locals = self.visible_locals_needed(&liveness.header, statement_span)?;
        let header = self.cfg.create_environment_block_with_extras(
            parent_scope,
            &header_locals,
            &[&predecessor],
            &fact_types,
            statement_span,
        )?;
        self.emit_drops_not_in_environment(&header, statement_span)?;
        let header_edge =
            header.target_from_with_extras(&predecessor, &predecessor_facts, statement_span)?;
        self.cfg.terminate_generated(
            VirTerminator::Jump {
                target: header_edge,
            },
            statement_span,
            VirGeneratedReason::ControlFlowEdge,
        )?;

        self.cfg.switch_to(header.block(), statement_span)?;
        self.environment = header.entry_environment();
        self.flow_facts = header.extra_parameters().to_vec();
        let lowered_condition = self.lower_condition(condition)?;
        if lowered_condition.value.ty != VirType::Bool
            || lowered_condition.value.permission.is_some()
        {
            return Err(invalid_hir(condition.span));
        }

        let mut branch_facts = self.flow_facts.clone();
        extend_unique_facts(&mut branch_facts, &lowered_condition.fact_values);
        let branch_fact_types = branch_facts
            .iter()
            .map(|value| value.ty)
            .collect::<Vec<_>>();
        let mut body_loops = outer_liveness;
        body_loops.push(liveness.clone());
        let body_live_in = block_live_in(body, &liveness.header, &body_loops)?;
        let mut body_locals = self.visible_locals_needed(&body_live_in, statement_span)?;
        self.retain_drop_locals(&mut body_locals);
        let body_target = self.cfg.create_environment_block_with_extras(
            body.scope,
            &body_locals,
            &[&self.environment],
            &branch_fact_types,
            body.span,
        )?;
        let exit_locals = self.visible_locals_needed(&liveness.exit, statement_span)?;
        let exit = self.cfg.create_environment_block_with_extras(
            parent_scope,
            &exit_locals,
            &[&self.environment],
            &fact_types,
            containing_block_span,
        )?;
        let condition_exit = self.cfg.create_environment_block_with_extras(
            parent_scope,
            &header_locals,
            &[&self.environment],
            &fact_types,
            statement_span,
        )?;
        let body_edge = body_target.target_from_with_extras(
            &self.environment,
            &branch_facts,
            statement_span,
        )?;
        let exit_edge = condition_exit.target_from_with_extras(
            &self.environment,
            &self.flow_facts,
            statement_span,
        )?;
        self.cfg.terminate(
            VirTerminator::Branch {
                condition: lowered_condition.value.value,
                then_target: body_edge,
                else_target: exit_edge,
            },
            statement_span,
        )?;

        let lowered_loop = LoweredLoop {
            liveness,
            parent_scope,
            continue_target: header,
            exit,
        };
        self.active_loops.push(lowered_loop.clone());
        let body_result = self.lower_loop_body(body, &body_target, &lowered_loop, None);
        if self
            .active_loops
            .pop()
            .is_none_or(|active| active.liveness.loop_id != loop_id)
        {
            return Err(invalid_hir(statement_span));
        }
        body_result?;

        self.lower_loop_condition_exit(&condition_exit, &lowered_loop.exit, statement_span)?;

        self.cfg
            .switch_to(lowered_loop.exit.block(), statement_span)?;
        self.environment = lowered_loop.exit.entry_environment();
        self.flow_facts = lowered_loop.exit.extra_parameters().to_vec();
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_for(
        &mut self,
        loop_id: HirLoopId,
        pattern: &HirPattern,
        source: &HirForSource,
        body: &HirBlock,
        statement_span: ByteSpan,
        containing_block_span: ByteSpan,
        live_after: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        if self
            .active_loops
            .iter()
            .any(|active| active.liveness.loop_id == loop_id)
        {
            return Err(invalid_hir(statement_span));
        }
        let HirForSource::IntegerRange {
            start,
            end,
            inclusive,
            item_type,
        } = source;
        let HirPatternKind::Binding { local: binding, .. } = &pattern.kind else {
            return Err(invalid_hir(pattern.span));
        };
        if *inclusive || *item_type != pattern.ty {
            return Err(invalid_hir(statement_span));
        }
        self.types
            .require_runtime_word(*item_type, statement_span)?;

        // Both bounds are evaluated exactly once, left-to-right, before any
        // loop block is entered.
        let start = self.lower_expression(start)?;
        let end = self.lower_expression(end)?;
        if start.ty != VirType::U64
            || end.ty != VirType::U64
            || start.permission.is_some()
            || end.permission.is_some()
        {
            return Err(invalid_hir(statement_span));
        }

        let outer_liveness = self.active_loop_liveness();
        let liveness =
            for_loop_liveness(loop_id, body, live_after, &outer_liveness, statement_span)?;
        let parent_scope = self
            .active_scopes
            .last()
            .copied()
            .ok_or_else(|| invalid_hir(statement_span))?;
        let predecessor = self.environment.clone();
        let predecessor_facts = self.flow_facts.clone();
        let predecessor_fact_count = predecessor_facts.len();
        let mut loop_facts = predecessor_facts.clone();
        loop_facts.push(VirValue {
            id: start.value,
            ty: start.ty,
        });
        loop_facts.push(VirValue {
            id: start.value,
            ty: start.ty,
        });
        loop_facts.push(VirValue {
            id: end.value,
            ty: end.ty,
        });
        let loop_fact_types = loop_facts.iter().map(|value| value.ty).collect::<Vec<_>>();
        let exit_fact_types = predecessor_facts
            .iter()
            .map(|value| value.ty)
            .collect::<Vec<_>>();
        let header_locals = self.visible_locals_needed(&liveness.header, statement_span)?;
        let header = self.cfg.create_environment_block_with_extras(
            parent_scope,
            &header_locals,
            &[&predecessor],
            &loop_fact_types,
            statement_span,
        )?;
        self.emit_drops_not_in_environment(&header, statement_span)?;
        let initial_edge =
            header.target_from_with_extras(&predecessor, &loop_facts, statement_span)?;
        self.cfg.terminate_generated(
            VirTerminator::Jump {
                target: initial_edge,
            },
            statement_span,
            VirGeneratedReason::ControlFlowEdge,
        )?;

        self.cfg.switch_to(header.block(), statement_span)?;
        self.environment = header.entry_environment();
        self.flow_facts = header.extra_parameters().to_vec();
        let current_index = predecessor_fact_count + 1;
        let end_index = predecessor_fact_count + 2;
        let current = *self
            .flow_facts
            .get(current_index)
            .ok_or_else(|| invalid_hir(statement_span))?;
        let end = *self
            .flow_facts
            .get(end_index)
            .ok_or_else(|| invalid_hir(statement_span))?;
        let condition =
            self.emit_integer_compare(VirIntegerPredicate::LessThan, current, end, statement_span)?;
        let mut branch_facts = self.flow_facts.clone();
        extend_unique_facts(&mut branch_facts, &condition.fact_values);
        let branch_fact_types = branch_facts
            .iter()
            .map(|value| value.ty)
            .collect::<Vec<_>>();

        let mut body_loops = outer_liveness;
        body_loops.push(liveness.clone());
        let body_live_in = block_live_in(body, &liveness.header, &body_loops)?;
        let mut body_locals = self.visible_locals_needed(&body_live_in, statement_span)?;
        self.retain_drop_locals(&mut body_locals);
        let body_target = self.cfg.create_environment_block_with_extras(
            body.scope,
            &body_locals,
            &[&self.environment],
            &branch_fact_types,
            body.span,
        )?;
        let latch = self.cfg.create_environment_block_with_extras(
            parent_scope,
            &header_locals,
            &[&self.environment],
            &loop_fact_types,
            statement_span,
        )?;
        let exit_locals = self.visible_locals_needed(&liveness.exit, statement_span)?;
        let exit = self.cfg.create_environment_block_with_extras(
            parent_scope,
            &exit_locals,
            &[&self.environment],
            &exit_fact_types,
            containing_block_span,
        )?;
        let condition_exit = self.cfg.create_environment_block_with_extras(
            parent_scope,
            &header_locals,
            &[&self.environment],
            &exit_fact_types,
            statement_span,
        )?;
        let body_edge = body_target.target_from_with_extras(
            &self.environment,
            &branch_facts,
            statement_span,
        )?;
        let exit_edge = condition_exit.target_from_with_extras(
            &self.environment,
            &self.flow_facts[..predecessor_fact_count],
            statement_span,
        )?;
        self.cfg.terminate(
            VirTerminator::Branch {
                condition: condition.value.value,
                then_target: body_edge,
                else_target: exit_edge,
            },
            statement_span,
        )?;

        let lowered_loop = LoweredLoop {
            liveness,
            parent_scope,
            continue_target: latch.clone(),
            exit,
        };
        self.active_loops.push(lowered_loop.clone());
        let body_result = self.lower_loop_body(
            body,
            &body_target,
            &lowered_loop,
            Some((*binding, current_index)),
        );
        if self
            .active_loops
            .pop()
            .is_none_or(|active| active.liveness.loop_id != loop_id)
        {
            return Err(invalid_hir(statement_span));
        }
        body_result?;

        self.cfg.switch_to(latch.block(), statement_span)?;
        self.environment = latch.entry_environment();
        self.flow_facts = latch.extra_parameters().to_vec();
        let current = *self
            .flow_facts
            .get(current_index)
            .ok_or_else(|| invalid_hir(statement_span))?;
        let one =
            self.lower_generated_integer(1, statement_span, VirGeneratedReason::LoopIncrement)?;
        let next = self.fresh_value(VirType::U64, statement_span)?;
        self.emit_generated(
            VirInstruction::WordAdd {
                result: next,
                left: current.id,
                right: one.value,
            },
            statement_span,
            VirGeneratedReason::LoopIncrement,
        )?;
        let mut next_facts = self.flow_facts.clone();
        next_facts[current_index] = next;
        let header_edge =
            header.target_from_with_extras(&self.environment, &next_facts, statement_span)?;
        self.cfg.terminate_generated(
            VirTerminator::Jump {
                target: header_edge,
            },
            statement_span,
            VirGeneratedReason::ControlFlowEdge,
        )?;

        self.lower_loop_condition_exit(&condition_exit, &lowered_loop.exit, statement_span)?;

        self.cfg
            .switch_to(lowered_loop.exit.block(), statement_span)?;
        self.environment = lowered_loop.exit.entry_environment();
        self.flow_facts = lowered_loop.exit.extra_parameters().to_vec();
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_match(
        &mut self,
        scrutinee: &HirExpression,
        arms: &[HirMatchArm],
        statement_span: ByteSpan,
        containing_block_span: ByteSpan,
        live_after: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        if arms.is_empty() {
            return Err(invalid_hir(statement_span));
        }
        let scrutinee_hir_type = scrutinee.ty;
        if matches!(
            self.hir.type_kind(scrutinee_hir_type),
            Some(HirTypeKind::Enum { .. })
        ) {
            return self.lower_enum_match(
                scrutinee,
                arms,
                statement_span,
                containing_block_span,
                live_after,
            );
        }
        match self.hir.type_kind(scrutinee_hir_type) {
            Some(HirTypeKind::Bool) => {
                self.types
                    .require_bool(scrutinee_hir_type, scrutinee.span)?;
            }
            Some(HirTypeKind::Integer(super::hir::HirIntegerType::U64)) => {
                self.types.require_u64(scrutinee_hir_type, scrutinee.span)?;
            }
            _ => return Err(invalid_hir(scrutinee.span)),
        }
        let scrutinee = self.lower_expression(scrutinee)?;
        if !matches!(scrutinee.ty, VirType::Bool | VirType::U64) || scrutinee.permission.is_some() {
            return Err(invalid_hir(statement_span));
        }

        let parent_scope = self
            .active_scopes
            .last()
            .copied()
            .ok_or_else(|| invalid_hir(statement_span))?;
        let predecessor = self.environment.clone();
        let predecessor_facts = self.flow_facts.clone();
        let mut chain_facts = predecessor_facts.clone();
        let scrutinee_fact = VirValue {
            id: scrutinee.value,
            ty: scrutinee.ty,
        };
        let scrutinee_fact_index = if let Some(index) = chain_facts
            .iter()
            .position(|fact| fact.id == scrutinee_fact.id)
        {
            index
        } else {
            let index = chain_facts.len();
            chain_facts.push(scrutinee_fact);
            index
        };
        let chain_fact_types = chain_facts.iter().map(|value| value.ty).collect::<Vec<_>>();
        self.flow_facts = chain_facts.clone();

        let active_loops = self.active_loop_liveness();
        let mut suffix_live = vec![Vec::new(); arms.len()];
        let mut suffix = BTreeSet::new();
        for (index, arm) in arms.iter().enumerate().rev() {
            suffix.extend(match_arm_live_in(arm, live_after, &active_loops)?);
            suffix_live[index] = suffix.iter().copied().collect();
        }
        let join_needed = arms.iter().any(|arm| block_falls_through(&arm.body));
        let join_locals = self.visible_locals_needed(live_after, statement_span)?;
        let join_fact_types = predecessor_facts
            .iter()
            .map(|value| value.ty)
            .collect::<Vec<_>>();
        let join = join_needed
            .then(|| {
                self.cfg.create_environment_block_with_extras(
                    parent_scope,
                    &join_locals,
                    &[&predecessor],
                    &join_fact_types,
                    containing_block_span,
                )
            })
            .transpose()?;

        let mut covered_false = false;
        let mut covered_true = false;
        let mut exhaustive = false;
        for (index, arm) in arms.iter().enumerate() {
            let supported = matches!(
                (&arm.pattern.kind, scrutinee.ty),
                (HirPatternKind::Wildcard, _)
                    | (HirPatternKind::Bool(_), VirType::Bool)
                    | (HirPatternKind::Integer(_), VirType::U64)
            );
            if exhaustive || arm.pattern.ty != scrutinee_hir_type || !supported {
                return Err(invalid_hir(arm.pattern.span));
            }

            let completes_coverage = if arm.guard.is_none() {
                match &arm.pattern.kind {
                    HirPatternKind::Wildcard => true,
                    HirPatternKind::Bool(false) => {
                        covered_false = true;
                        covered_true
                    }
                    HirPatternKind::Bool(true) => {
                        covered_true = true;
                        covered_false
                    }
                    HirPatternKind::Integer(_)
                    | HirPatternKind::Binding { .. }
                    | HirPatternKind::Tuple(_)
                    | HirPatternKind::Variant { .. } => false,
                }
            } else {
                false
            };
            exhaustive = completes_coverage;

            let next = if completes_coverage {
                None
            } else {
                let Some(next_arm) = arms.get(index + 1) else {
                    return Err(invalid_hir(arm.span));
                };
                let mut next_locals =
                    self.visible_locals_needed(&suffix_live[index + 1], next_arm.span)?;
                self.retain_drop_locals(&mut next_locals);
                Some(self.cfg.create_environment_block_with_extras(
                    parent_scope,
                    &next_locals,
                    &[&self.environment],
                    &chain_fact_types,
                    next_arm.span,
                )?)
            };

            let (pattern_condition, matched_on_true, mut pattern_facts) = if completes_coverage {
                (None, true, chain_facts.clone())
            } else {
                let current_scrutinee = *chain_facts
                    .get(scrutinee_fact_index)
                    .filter(|value| value.ty == scrutinee.ty)
                    .ok_or_else(|| invalid_hir(arm.span))?;
                self.lower_match_pattern_test(&arm.pattern, current_scrutinee, &chain_facts)?
            };
            let pattern_fact_types = pattern_facts
                .iter()
                .map(|value| value.ty)
                .collect::<Vec<_>>();
            let arm_live = match_arm_live_in(arm, live_after, &active_loops)?;
            let mut arm_locals = self.visible_locals_needed(&arm_live, arm.span)?;
            self.retain_drop_locals(&mut arm_locals);

            if let Some(guard) = &arm.guard {
                let guard_target = self.cfg.create_environment_block_with_extras(
                    parent_scope,
                    &arm_locals,
                    &[&self.environment],
                    &pattern_fact_types,
                    arm.span,
                )?;
                self.terminate_match_test(
                    pattern_condition,
                    matched_on_true,
                    &guard_target,
                    next.as_ref(),
                    &pattern_facts,
                    &chain_facts,
                    arm.pattern.span,
                )?;

                self.cfg.switch_to(guard_target.block(), arm.span)?;
                self.environment = guard_target.entry_environment();
                self.flow_facts = guard_target.extra_parameters().to_vec();
                let lowered_guard = self.lower_condition(guard)?;
                if lowered_guard.value.ty != VirType::Bool
                    || lowered_guard.value.permission.is_some()
                {
                    return Err(invalid_hir(guard.span));
                }
                pattern_facts = self.flow_facts.clone();
                extend_unique_facts(&mut pattern_facts, &lowered_guard.fact_values);
                let guarded_fact_types = pattern_facts
                    .iter()
                    .map(|value| value.ty)
                    .collect::<Vec<_>>();
                let body_live = block_live_in(&arm.body, live_after, &active_loops)?;
                let mut body_locals = self.visible_locals_needed(&body_live, arm.span)?;
                self.retain_drop_locals(&mut body_locals);
                let body_target = self.cfg.create_environment_block_with_extras(
                    arm.body.scope,
                    &body_locals,
                    &[&self.environment],
                    &guarded_fact_types,
                    arm.body.span,
                )?;
                let then_target = body_target.target_from_with_extras(
                    &self.environment,
                    &pattern_facts,
                    guard.span,
                )?;
                let next = next.as_ref().ok_or_else(|| invalid_hir(arm.span))?;
                let false_facts = self
                    .flow_facts
                    .get(..chain_facts.len())
                    .ok_or_else(|| invalid_hir(guard.span))?;
                let else_target =
                    next.target_from_with_extras(&self.environment, false_facts, guard.span)?;
                self.cfg.terminate(
                    VirTerminator::Branch {
                        condition: lowered_guard.value.value,
                        then_target,
                        else_target,
                    },
                    guard.span,
                )?;
                self.lower_branch_block(&arm.body, &body_target, join.as_ref(), live_after)?;
            } else {
                let body_live = block_live_in(&arm.body, live_after, &active_loops)?;
                let mut body_locals = self.visible_locals_needed(&body_live, arm.span)?;
                self.retain_drop_locals(&mut body_locals);
                let body_target = self.cfg.create_environment_block_with_extras(
                    arm.body.scope,
                    &body_locals,
                    &[&self.environment],
                    &pattern_fact_types,
                    arm.body.span,
                )?;
                self.terminate_match_test(
                    pattern_condition,
                    matched_on_true,
                    &body_target,
                    next.as_ref(),
                    &pattern_facts,
                    &chain_facts,
                    arm.pattern.span,
                )?;
                self.lower_branch_block(&arm.body, &body_target, join.as_ref(), live_after)?;
            }

            if let Some(next) = next {
                let next_span = arms.get(index + 1).map_or(statement_span, |arm| arm.span);
                self.cfg.switch_to(next.block(), next_span)?;
                self.environment = next.entry_environment();
                self.flow_facts = next.extra_parameters().to_vec();
                chain_facts = self.flow_facts.clone();
            }
        }
        if !exhaustive {
            return Err(invalid_hir(statement_span));
        }

        if let Some(join) = join {
            self.cfg.switch_to(join.block(), statement_span)?;
            self.environment = join.entry_environment();
            self.flow_facts = join.extra_parameters().to_vec();
        } else {
            self.environment = predecessor;
            self.flow_facts = predecessor_facts;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_enum_match(
        &mut self,
        scrutinee: &HirExpression,
        arms: &[HirMatchArm],
        statement_span: ByteSpan,
        containing_block_span: ByteSpan,
        live_after: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        let Some(HirTypeKind::Enum {
            variants: declared_variants,
        }) = self.hir.type_kind(scrutinee.ty)
        else {
            return Err(invalid_hir(scrutinee.span));
        };
        let declared_variants = declared_variants.clone();
        let object = self.lower_object_expression(scrutinee)?;
        let expected_access = self.memory.access(scrutinee.ty, scrutinee.span)?;
        if object.access != expected_access {
            return Err(invalid_hir(scrutinee.span));
        }
        let tag = self.fresh_value(VirType::U64, scrutinee.span)?;
        self.emit(
            VirInstruction::EnumDiscriminant {
                result: tag,
                pointer: object.pointer,
                permission: object.permission,
                access: object.access,
            },
            scrutinee.span,
        )?;

        let parent_scope = self
            .active_scopes
            .last()
            .copied()
            .ok_or_else(|| invalid_hir(statement_span))?;
        let predecessor = self.environment.clone();
        let predecessor_facts = self.flow_facts.clone();
        let mut chain_facts = predecessor_facts.clone();
        let tag_index = if let Some(index) = chain_facts.iter().position(|fact| fact.id == tag.id) {
            index
        } else {
            let index = chain_facts.len();
            chain_facts.push(tag);
            index
        };
        let chain_fact_types = chain_facts.iter().map(|value| value.ty).collect::<Vec<_>>();
        self.flow_facts = chain_facts.clone();

        let active_loops = self.active_loop_liveness();
        let mut suffix_live = vec![Vec::new(); arms.len()];
        let mut suffix = BTreeSet::new();
        for (index, arm) in arms.iter().enumerate().rev() {
            suffix.extend(match_arm_live_in(arm, live_after, &active_loops)?);
            suffix_live[index] = suffix.iter().copied().collect();
        }
        let join_needed = arms.iter().any(|arm| block_falls_through(&arm.body));
        let join_locals = self.visible_locals_needed(live_after, statement_span)?;
        let join_fact_types = predecessor_facts
            .iter()
            .map(|value| value.ty)
            .collect::<Vec<_>>();
        let join = join_needed
            .then(|| {
                self.cfg.create_environment_block_with_extras(
                    parent_scope,
                    &join_locals,
                    &[&predecessor],
                    &join_fact_types,
                    containing_block_span,
                )
            })
            .transpose()?;

        let mut covered = BTreeSet::new();
        let mut exhaustive = false;
        for (index, arm) in arms.iter().enumerate() {
            if exhaustive || arm.pattern.ty != scrutinee.ty || arm.guard.is_some() {
                return Err(invalid_hir(arm.span));
            }
            let variant = match &arm.pattern.kind {
                HirPatternKind::Wildcard => None,
                HirPatternKind::Variant { variant, .. }
                    if declared_variants.contains(variant)
                        && self
                            .hir
                            .variant(*variant)
                            .is_some_and(|variant| variant.owner == scrutinee.ty) =>
                {
                    Some(*variant)
                }
                _ => return Err(invalid_hir(arm.pattern.span)),
            };
            let completes_coverage = if let Some(variant) = variant {
                if !covered.insert(variant) {
                    return Err(invalid_hir(arm.pattern.span));
                }
                declared_variants
                    .iter()
                    .all(|variant| covered.contains(variant))
            } else {
                true
            };
            exhaustive = completes_coverage;

            let next = if completes_coverage {
                None
            } else {
                let next_arm = arms.get(index + 1).ok_or_else(|| invalid_hir(arm.span))?;
                let mut next_locals =
                    self.visible_locals_needed(&suffix_live[index + 1], next_arm.span)?;
                self.retain_drop_locals(&mut next_locals);
                Some(self.cfg.create_environment_block_with_extras(
                    parent_scope,
                    &next_locals,
                    &[&self.environment],
                    &chain_fact_types,
                    next_arm.span,
                )?)
            };

            let mut pattern_facts = chain_facts.clone();
            let condition = if completes_coverage {
                None
            } else {
                let variant = variant.ok_or_else(|| invalid_hir(arm.pattern.span))?;
                let discriminant = self
                    .hir
                    .variant(variant)
                    .map(|variant| variant.discriminant)
                    .ok_or_else(|| invalid_hir(arm.pattern.span))?;
                let constant = self.lower_integer(discriminant, arm.pattern.span)?;
                let current_tag = *chain_facts
                    .get(tag_index)
                    .filter(|value| value.ty == VirType::U64)
                    .ok_or_else(|| invalid_hir(arm.pattern.span))?;
                let comparison = self.emit_integer_compare(
                    VirIntegerPredicate::Equal,
                    current_tag,
                    VirValue {
                        id: constant.value,
                        ty: constant.ty,
                    },
                    arm.pattern.span,
                )?;
                extend_unique_facts(&mut pattern_facts, &comparison.fact_values);
                Some(comparison.value.value)
            };
            let pattern_fact_types = pattern_facts
                .iter()
                .map(|value| value.ty)
                .collect::<Vec<_>>();
            let body_live = block_live_in(&arm.body, live_after, &active_loops)?;
            let mut body_locals = self.visible_locals_needed(&body_live, arm.span)?;
            self.retain_drop_locals(&mut body_locals);
            let body_target = self.cfg.create_environment_block_with_extras(
                arm.body.scope,
                &body_locals,
                &[&self.environment],
                &pattern_fact_types,
                arm.span,
            )?;
            self.terminate_match_test(
                condition,
                true,
                &body_target,
                next.as_ref(),
                &pattern_facts,
                &chain_facts,
                arm.pattern.span,
            )?;
            self.lower_enum_branch_block(
                scrutinee,
                &arm.pattern,
                &arm.body,
                &body_target,
                join.as_ref(),
                live_after,
            )?;

            if let Some(next) = next {
                let next_span = arms.get(index + 1).map_or(statement_span, |arm| arm.span);
                self.cfg.switch_to(next.block(), next_span)?;
                self.environment = next.entry_environment();
                self.flow_facts = next.extra_parameters().to_vec();
                chain_facts = self.flow_facts.clone();
            }
        }
        if !exhaustive {
            return Err(invalid_hir(statement_span));
        }
        if let Some(join) = join {
            self.cfg.switch_to(join.block(), statement_span)?;
            self.environment = join.entry_environment();
            self.flow_facts = join.extra_parameters().to_vec();
        } else {
            self.environment = predecessor;
            self.flow_facts = predecessor_facts;
        }
        Ok(())
    }

    fn lower_enum_branch_block(
        &mut self,
        scrutinee: &HirExpression,
        pattern: &HirPattern,
        block: &HirBlock,
        entry: &EnvironmentBlock,
        join: Option<&EnvironmentBlock>,
        live_after: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        self.cfg.switch_to(entry.block(), block.span)?;
        self.environment = entry.entry_environment();
        self.flow_facts = entry.extra_parameters().to_vec();
        let retained_scope = self
            .active_scopes
            .last()
            .copied()
            .ok_or_else(|| invalid_hir(block.span))?;
        self.enter_scope(block)?;
        let object = self.lower_object_expression(scrutinee)?;
        self.lower_enum_pattern_bindings(object, pattern)?;
        self.lower_block_statements(block, live_after)?;
        if self.cfg.has_open_block() {
            let join = join.ok_or_else(|| invalid_hir(block.span))?;
            self.emit_drops_not_in_environment(join, block.span)?;
            let facts = self
                .flow_facts
                .get(..join.extra_parameters().len())
                .ok_or_else(|| invalid_hir(block.span))?;
            let target = join.target_from_with_extras(&self.environment, facts, block.span)?;
            self.terminate_scope_exit(
                Some(retained_scope),
                VirTerminator::Jump { target },
                block.span,
                true,
            )?;
        }
        self.leave_scope(block)
    }

    fn lower_enum_pattern_bindings(
        &mut self,
        object: LoweredObject,
        pattern: &HirPattern,
    ) -> Result<(), FrontendFailure> {
        let HirPatternKind::Variant { variant, fields } = &pattern.kind else {
            return matches!(pattern.kind, HirPatternKind::Wildcard)
                .then_some(())
                .ok_or_else(|| invalid_hir(pattern.span));
        };
        let variant_definition = self
            .hir
            .variant(*variant)
            .cloned()
            .ok_or_else(|| invalid_hir(pattern.span))?;
        if variant_definition.fields.len() != fields.len() {
            return Err(invalid_hir(pattern.span));
        }
        for (field_id, field_pattern) in variant_definition.fields.iter().zip(fields) {
            let field = self
                .hir
                .field(*field_id)
                .cloned()
                .ok_or_else(|| invalid_hir(field_pattern.span))?;
            if field.ty != field_pattern.ty {
                return Err(invalid_hir(field_pattern.span));
            }
            match &field_pattern.kind {
                HirPatternKind::Wildcard => {}
                HirPatternKind::Binding { local, mode } => {
                    let source =
                        self.field_object(object, *field_id, Some(*variant), field_pattern.span)?;
                    if self
                        .types
                        .aggregate_access(&self.memory, field.ty, field_pattern.span)?
                        .is_some()
                    {
                        let destination = self.storage_object(*local, field_pattern.span)?;
                        self.emit_object_assignment(
                            destination,
                            source,
                            vir_object_source_mode(*mode),
                            DraftSourceIdentity::HirNode(field_pattern.id),
                            field_pattern.span,
                        )?;
                    } else {
                        let address = LoweredAddress {
                            pointer: source.pointer,
                            permission: source.permission,
                            metadata: None,
                            ty: field.ty,
                        };
                        let value = self.lower_address_read(address, *mode, field_pattern.span)?;
                        self.assign_local(*local, value, field_pattern.span)?;
                    }
                }
                HirPatternKind::Integer(_)
                | HirPatternKind::Bool(_)
                | HirPatternKind::Tuple(_)
                | HirPatternKind::Variant { .. } => {
                    return Err(invalid_hir(field_pattern.span));
                }
            }
        }
        Ok(())
    }

    fn lower_match_pattern_test(
        &mut self,
        pattern: &HirPattern,
        scrutinee: VirValue,
        chain_facts: &[VirValue],
    ) -> Result<(Option<VirValueId>, bool, Vec<VirValue>), FrontendFailure> {
        match (&pattern.kind, scrutinee.ty) {
            (HirPatternKind::Wildcard, _) => Ok((None, true, chain_facts.to_vec())),
            (HirPatternKind::Bool(value), VirType::Bool) => {
                let mut facts = chain_facts.to_vec();
                extend_unique_facts(&mut facts, &[scrutinee]);
                Ok((Some(scrutinee.id), *value, facts))
            }
            (HirPatternKind::Integer(value), VirType::U64) => {
                let constant = self.lower_integer(*value, pattern.span)?;
                let comparison = self.emit_integer_compare(
                    VirIntegerPredicate::Equal,
                    scrutinee,
                    VirValue {
                        id: constant.value,
                        ty: constant.ty,
                    },
                    pattern.span,
                )?;
                let mut facts = chain_facts.to_vec();
                extend_unique_facts(&mut facts, &comparison.fact_values);
                Ok((Some(comparison.value.value), true, facts))
            }
            _ => Err(invalid_hir(pattern.span)),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn terminate_match_test(
        &mut self,
        condition: Option<VirValueId>,
        matched_on_true: bool,
        matched: &EnvironmentBlock,
        next: Option<&EnvironmentBlock>,
        matched_facts: &[VirValue],
        chain_facts: &[VirValue],
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let matched_target =
            matched.target_from_with_extras(&self.environment, matched_facts, source_span)?;
        match condition {
            None => self.cfg.terminate(
                VirTerminator::Jump {
                    target: matched_target,
                },
                source_span,
            ),
            Some(condition) => {
                let next = next.ok_or_else(|| invalid_hir(source_span))?;
                let next_target =
                    next.target_from_with_extras(&self.environment, chain_facts, source_span)?;
                let (then_target, else_target) = if matched_on_true {
                    (matched_target, next_target)
                } else {
                    (next_target, matched_target)
                };
                self.cfg.terminate(
                    VirTerminator::Branch {
                        condition,
                        then_target,
                        else_target,
                    },
                    source_span,
                )
            }
        }
    }

    fn lower_loop_body(
        &mut self,
        body: &HirBlock,
        entry: &EnvironmentBlock,
        active: &LoweredLoop,
        entry_binding: Option<(HirLocalId, usize)>,
    ) -> Result<(), FrontendFailure> {
        self.cfg.switch_to(entry.block(), body.span)?;
        self.environment = entry.entry_environment();
        self.flow_facts = entry.extra_parameters().to_vec();
        self.enter_scope(body)?;
        if let Some((local, fact_index)) = entry_binding {
            let value = *self
                .flow_facts
                .get(fact_index)
                .ok_or_else(|| invalid_hir(body.span))?;
            self.assign_local(local, runtime_value(value), body.span)?;
        }
        self.lower_block_statements(body, &active.liveness.header)?;
        if self.cfg.has_open_block() {
            self.emit_drops_not_in_environment(&active.continue_target, body.span)?;
            let facts = self
                .flow_facts
                .get(..active.continue_target.extra_parameters().len())
                .ok_or_else(|| invalid_hir(body.span))?;
            let target = active.continue_target.target_from_with_extras(
                &self.environment,
                facts,
                body.span,
            )?;
            self.terminate_scope_exit(
                Some(active.parent_scope),
                VirTerminator::Jump { target },
                body.span,
                true,
            )?;
        }
        self.leave_scope(body)
    }

    fn lower_loop_exit(
        &mut self,
        target: HirLoopId,
        is_break: bool,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let active = self
            .active_loops
            .iter()
            .rev()
            .find(|active| active.liveness.loop_id == target)
            .cloned()
            .ok_or_else(|| invalid_hir(source_span))?;
        let destination = if is_break {
            &active.exit
        } else {
            &active.continue_target
        };
        self.emit_drops_not_in_environment(destination, source_span)?;
        let facts = self
            .flow_facts
            .get(..destination.extra_parameters().len())
            .ok_or_else(|| invalid_hir(source_span))?;
        let target = destination.target_from_with_extras(&self.environment, facts, source_span)?;
        self.terminate_scope_exit(
            Some(active.parent_scope),
            VirTerminator::Jump { target },
            source_span,
            false,
        )
    }

    fn lower_loop_condition_exit(
        &mut self,
        cleanup: &EnvironmentBlock,
        exit: &EnvironmentBlock,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        self.cfg.switch_to(cleanup.block(), source_span)?;
        self.environment = cleanup.entry_environment();
        self.flow_facts = cleanup.extra_parameters().to_vec();
        self.emit_drops_not_in_environment(exit, source_span)?;
        let facts = self
            .flow_facts
            .get(..exit.extra_parameters().len())
            .ok_or_else(|| invalid_hir(source_span))?;
        let target = exit.target_from_with_extras(&self.environment, facts, source_span)?;
        self.cfg.terminate_generated(
            VirTerminator::Jump { target },
            source_span,
            VirGeneratedReason::ControlFlowEdge,
        )
    }

    fn active_loop_liveness(&self) -> Vec<LoopLiveness> {
        self.active_loops
            .iter()
            .map(|active| active.liveness.clone())
            .collect()
    }

    fn lower_branch_block(
        &mut self,
        block: &HirBlock,
        entry: &EnvironmentBlock,
        join: Option<&EnvironmentBlock>,
        live_after: &[HirLocalId],
    ) -> Result<(), FrontendFailure> {
        self.cfg.switch_to(entry.block(), block.span)?;
        self.environment = entry.entry_environment();
        self.flow_facts = entry.extra_parameters().to_vec();
        let retained_scope = self
            .active_scopes
            .last()
            .copied()
            .ok_or_else(|| invalid_hir(block.span))?;
        self.enter_scope(block)?;
        self.lower_block_statements(block, live_after)?;
        if self.cfg.has_open_block() {
            let join = join.ok_or_else(|| invalid_hir(block.span))?;
            self.emit_drops_not_in_environment(join, block.span)?;
            let facts = self
                .flow_facts
                .get(..join.extra_parameters().len())
                .ok_or_else(|| invalid_hir(block.span))?;
            let target = join.target_from_with_extras(&self.environment, facts, block.span)?;
            self.terminate_scope_exit(
                Some(retained_scope),
                VirTerminator::Jump { target },
                block.span,
                true,
            )?;
        }
        self.leave_scope(block)
    }

    fn lower_empty_branch(
        &mut self,
        entry: &EnvironmentBlock,
        join: Option<&EnvironmentBlock>,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let join = join.ok_or_else(|| invalid_hir(source_span))?;
        self.cfg.switch_to(entry.block(), source_span)?;
        self.environment = entry.entry_environment();
        self.flow_facts = entry.extra_parameters().to_vec();
        self.emit_drops_not_in_environment(join, source_span)?;
        let facts = self
            .flow_facts
            .get(..join.extra_parameters().len())
            .ok_or_else(|| invalid_hir(source_span))?;
        let target = join.target_from_with_extras(&self.environment, facts, source_span)?;
        self.cfg.terminate_generated(
            VirTerminator::Jump { target },
            source_span,
            VirGeneratedReason::ControlFlowEdge,
        )
    }

    fn retain_conditional_drop_locals(
        &self,
        left: &mut Vec<HirLocalId>,
        right: &mut Vec<HirLocalId>,
    ) {
        let all = left
            .iter()
            .copied()
            .chain(right.iter().copied())
            .chain(self.active_drop_locals())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        *left = all.clone();
        *right = all;
    }

    fn retain_drop_locals(&self, locals: &mut Vec<HirLocalId>) {
        *locals = locals
            .iter()
            .copied()
            .chain(self.active_drop_locals())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
    }

    fn active_drop_locals(&self) -> impl Iterator<Item = HirLocalId> + '_ {
        (0..self.environment.len()).filter_map(|index| {
            let local = HirLocalId::new(u32::try_from(index).ok()?);
            self.environment.optional(local).and_then(|value| {
                value.drop_flag.and_then(|flag| {
                    (self.known_drop_flags.get(&flag) != Some(&false)).then_some(local)
                })
            })
        })
    }

    fn emit_drops_not_in_environment(
        &mut self,
        retained: &EnvironmentBlock,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let body = self
            .function
            .body()
            .ok_or_else(|| invalid_hir(source_span))?;
        let locals = body
            .locals
            .iter()
            .rev()
            .filter(|local| self.active_scopes.contains(&local.scope))
            .map(|local| local.id)
            .filter(|local| !retained.contains_local(*local))
            .collect::<Vec<_>>();
        for local in locals {
            self.emit_local_drop(local, source_span)?;
        }
        Ok(())
    }

    fn terminate_scope_exit(
        &mut self,
        retained_scope: Option<HirScopeId>,
        terminator: VirTerminator,
        source_span: ByteSpan,
        generated_edge: bool,
    ) -> Result<(), FrontendFailure> {
        self.emit_scope_exit_actions(retained_scope, source_span)?;
        if generated_edge {
            self.cfg.terminate_generated(
                terminator,
                source_span,
                VirGeneratedReason::ControlFlowEdge,
            )
        } else {
            self.cfg.terminate(terminator, source_span)
        }
    }

    fn emit_scope_exit_actions(
        &mut self,
        retained_scope: Option<HirScopeId>,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let plan = ScopeExitPlan::new(&self.active_scopes, retained_scope, source_span)?;
        let body = self
            .function
            .body()
            .ok_or_else(|| invalid_hir(source_span))?;
        let cleanup_locals = plan
            .leaving_scopes()
            .iter()
            .flat_map(|scope| {
                body.locals
                    .iter()
                    .rev()
                    .filter(move |local| local.scope == *scope)
                    .map(|local| local.id)
            })
            .collect::<Vec<_>>();
        for local in cleanup_locals {
            self.emit_local_drop(local, source_span)?;
        }
        Ok(())
    }

    fn emit_local_drop(
        &mut self,
        local: HirLocalId,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let Some(mut value) = self.environment.optional(local) else {
            return Ok(());
        };
        if let Some(loan) = value.loan {
            let permission = value.permission.ok_or_else(|| invalid_hir(source_span))?;
            match loan {
                LoweredLoan::Static(metadata) => self.cfg.emit_loan_end(
                    loan_effect(metadata, value.value, permission),
                    DraftSourceIdentity::LocalCleanup(local),
                    source_span,
                )?,
                LoweredLoan::Authority { reference, .. } => self.cfg.emit_loan_authority_end(
                    loan_authority_effect(value.value, permission, reference),
                    DraftSourceIdentity::LocalCleanup(local),
                    source_span,
                )?,
                LoweredLoan::ConditionalAuthority {
                    reference,
                    deferred,
                    ..
                } => {
                    self.emit_generated(
                        VirInstruction::LoanEndAuthority {
                            effect: loan_authority_effect(value.value, permission, reference),
                        },
                        source_span,
                        VirGeneratedReason::LoanEffect,
                    )?;
                    for deferred in deferred.into_iter().flatten() {
                        match deferred {
                            DeferredLoanEnd::Static {
                                loan,
                                pointer,
                                permission,
                            } => self.emit_generated(
                                VirInstruction::LoanEnd {
                                    effect: loan_effect(loan, pointer, permission),
                                },
                                source_span,
                                VirGeneratedReason::LoanEffect,
                            )?,
                            DeferredLoanEnd::Authority {
                                reference,
                                pointer,
                                permission,
                            } => self.emit_generated(
                                VirInstruction::LoanEndAuthority {
                                    effect: loan_authority_effect(pointer, permission, reference),
                                },
                                source_span,
                                VirGeneratedReason::LoanEffect,
                            )?,
                        }
                    }
                }
            }
            value.loan = None;
            self.environment.reassign(local, value, source_span)?;
        }
        let Some(condition) = value.drop_flag else {
            return Ok(());
        };
        if self.known_drop_flags.get(&condition) == Some(&false) {
            return Ok(());
        }
        let permission = value.permission.ok_or_else(|| invalid_hir(source_span))?;
        let kind = if self.storage_locals.contains(&local) {
            PendingCleanupKind::Object {
                condition: Some(condition),
            }
        } else {
            self.emit_pointee_cleanup(local, value, Some(condition), source_span)?;
            PendingCleanupKind::OwnedAllocation { condition }
        };
        let VirType::Pointer { access } = value.ty else {
            return Err(invalid_hir(source_span));
        };
        self.cfg.emit_cleanup(
            kind,
            DraftObjectIdentity {
                pointer: value.value,
                permission,
                access,
            },
            DraftSourceIdentity::LocalCleanup(local),
            source_span,
        )?;
        self.set_local_drop_flag(local, false, source_span)
    }

    /// Both explicit free and lexical owner cleanup retire present pointee
    /// resources before consuming the outer allocation capability. These are
    /// ordinary VIR effects, independently checked by every consumer.
    fn emit_pointee_cleanup(
        &mut self,
        local: HirLocalId,
        value: LoweredValue,
        condition: Option<VirValueId>,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let VirType::Pointer { access } = value.ty else {
            return Err(invalid_hir(source_span));
        };
        let shape = self
            .memory
            .schema()
            .object_shape(access)
            .map_err(|_| invalid_hir(source_span))?;
        if shape.resource_leaves().is_empty() {
            return Ok(());
        }
        let condition = match condition {
            Some(condition) => condition,
            None => self.lower_generated_drop_flag(true, source_span)?,
        };
        self.cfg.emit_cleanup(
            PendingCleanupKind::Object {
                condition: Some(condition),
            },
            DraftObjectIdentity {
                pointer: value.value,
                permission: value.permission.ok_or_else(|| invalid_hir(source_span))?,
                access,
            },
            DraftSourceIdentity::LocalCleanup(local),
            source_span,
        )
    }

    fn enter_scope(&mut self, block: &HirBlock) -> Result<(), FrontendFailure> {
        if self.active_scopes.contains(&block.scope) {
            return Err(invalid_hir(block.span));
        }
        let scalar_locals = block
            .locals
            .iter()
            .copied()
            .filter(|local| !self.storage_locals.contains(local))
            .collect::<Vec<_>>();
        self.environment
            .require_uninitialized(&scalar_locals, block.span)?;
        self.active_scopes.push(block.scope);
        Ok(())
    }

    fn leave_scope(&mut self, block: &HirBlock) -> Result<(), FrontendFailure> {
        if self.active_scopes.pop() != Some(block.scope) {
            return Err(invalid_hir(block.span));
        }
        let scalar_locals = block
            .locals
            .iter()
            .copied()
            .filter(|local| !self.storage_locals.contains(local))
            .collect::<Vec<_>>();
        self.environment.forget(&scalar_locals, block.span)
    }

    fn visible_locals_needed(
        &self,
        needed: &[HirLocalId],
        source_span: ByteSpan,
    ) -> Result<Vec<HirLocalId>, FrontendFailure> {
        let body = self
            .function
            .body()
            .ok_or_else(|| invalid_hir(source_span))?;
        let requested = needed.iter().copied().collect::<BTreeSet<_>>();
        if requested.len() != needed.len() {
            return Err(invalid_hir(source_span));
        }
        let hidden = self
            .object_temporaries
            .iter()
            .map(|storage| storage.local)
            .chain(self.abi_call_storage.iter().map(|storage| storage.local))
            .chain(self.abi_indirect_result)
            .collect::<BTreeSet<_>>();
        let active_loans = body
            .locals
            .iter()
            .filter(|local| self.active_scopes.contains(&local.scope))
            .filter_map(|local| {
                self.environment
                    .optional(local.id)
                    .is_some_and(|value| value.loan.is_some())
                    .then_some(local.id)
            })
            .collect::<BTreeSet<_>>();
        let expected = requested
            .iter()
            .copied()
            .chain(self.storage_locals.iter().copied())
            .chain(active_loans.iter().copied())
            .chain(hidden.iter().copied())
            .collect::<BTreeSet<_>>();
        let mut locals = body
            .locals
            .iter()
            .filter(|local| {
                self.storage_locals.contains(&local.id)
                    || active_loans.contains(&local.id)
                    || (self.active_scopes.contains(&local.scope) && requested.contains(&local.id))
            })
            .map(|local| local.id)
            .collect::<Vec<_>>();
        locals.extend(hidden);
        if locals != expected.into_iter().collect::<Vec<_>>() {
            return Err(invalid_hir(source_span));
        }
        Ok(locals)
    }

    fn lower_expression(
        &mut self,
        expression: &HirExpression,
    ) -> Result<LoweredValue, FrontendFailure> {
        let value = match &expression.kind {
            HirExpressionKind::Unit => return Err(invalid_hir(expression.span)),
            HirExpressionKind::Integer(word) => {
                self.types
                    .require_runtime_word(expression.ty, expression.span)?;
                self.lower_integer(*word, expression.span)?
            }
            HirExpressionKind::Bool(value) => {
                self.types.require_bool(expression.ty, expression.span)?;
                self.lower_bool(*value, expression.span)?
            }
            HirExpressionKind::Length { place } => {
                let selected = self.lower_place(place, HirPlaceAccess::Read, expression.span)?;
                let ty = match self.hir.type_kind(place.ty) {
                    Some(HirTypeKind::Reference { pointee, .. }) => *pointee,
                    _ => place.ty,
                };
                if let Some(HirTypeKind::Array { length, .. }) = self.hir.type_kind(ty) {
                    self.lower_integer(*length, expression.span)?
                } else {
                    let length = match selected {
                        LoweredPlace::Local(local) => {
                            self.lookup_local(local, expression.span)?.metadata
                        }
                        LoweredPlace::Address(address) => address.metadata,
                        _ => None,
                    }
                    .ok_or_else(|| invalid_hir(expression.span))?;
                    LoweredValue {
                        value: length,
                        ty: VirType::U64,
                        metadata: None,
                        permission: None,
                        drop_flag: None,
                        loan: None,
                    }
                }
            }
            HirExpressionKind::TupleConstructor { .. }
            | HirExpressionKind::ArrayConstructor { .. }
            | HirExpressionKind::ArrayRepeatConstructor { .. }
            | HirExpressionKind::StructConstructor { .. }
            | HirExpressionKind::EnumConstructor { .. } => {
                return Err(invalid_hir(expression.span));
            }
            HirExpressionKind::Compare {
                predicate,
                left,
                right,
                operation_span,
            } => self.lower_compare(*predicate, left, right, *operation_span, expression.span)?,
            HirExpressionKind::PointerDistance { begin, end } => {
                if !self.types.matching_raw_pointers(begin.ty, end.ty) {
                    return Err(invalid_hir(expression.span));
                }
                self.types
                    .require_runtime_word(expression.ty, expression.span)?;
                let begin = self.lower_expression(begin)?;
                let end = self.lower_expression(end)?;
                let result = self.fresh_value(VirType::U64, expression.span)?;
                self.emit(
                    VirInstruction::PointerDistance {
                        result,
                        begin: begin.value,
                        end: end.value,
                    },
                    expression.span,
                )?;
                runtime_value(result)
            }
            HirExpressionKind::Allocate {
                element_type,
                element_count,
                size_bytes,
                alignment,
            } => {
                self.types.validate_allocation(
                    expression.ty,
                    *element_type,
                    *element_count,
                    *size_bytes,
                    *alignment,
                    expression.span,
                )?;
                self.lower_allocate(*element_type, *size_bytes, *alignment, expression.span)?
            }
            HirExpressionKind::OwnerAddress { place } => {
                let LoweredPlace::Local(local) =
                    self.lower_place(place, HirPlaceAccess::Read, expression.span)?
                else {
                    return Err(invalid_hir(expression.span));
                };
                let mut value = self.lookup_local(local, expression.span)?;
                value.drop_flag = None;
                value
            }
            HirExpressionKind::Read { place, mode } => {
                self.lower_read(place, *mode, expression.span)?
            }
            HirExpressionKind::Borrow {
                place,
                mutability,
                region,
            } => self.lower_borrow(place, *mutability, *region, expression.ty, expression.span)?,
            HirExpressionKind::RawAddress { place, mutability } => {
                self.lower_raw_address(place, *mutability, expression.ty, expression.span)?
            }
            HirExpressionKind::WordAdd {
                operands,
                operation_spans,
            } => {
                self.types
                    .require_runtime_word(expression.ty, expression.span)?;
                self.lower_word_add(operands, operation_spans, expression.span)?
            }
            HirExpressionKind::PointerOffset { base, offsets } => {
                self.types.validate_pointer_offset(
                    expression.ty,
                    base.ty,
                    offsets.len(),
                    expression.span,
                )?;
                let mut accumulated = self.lower_expression(base)?;
                for offset in offsets {
                    accumulated =
                        self.lower_pointer_offset(accumulated, offset.delta_bytes, offset.span)?;
                }
                accumulated
            }
            HirExpressionKind::Call(call) => self
                .lower_call(expression, call, expression.span)?
                .ok_or_else(|| invalid_hir(expression.span))?,
        };
        let expected = self
            .types
            .value_type(&self.memory, expression.ty, expression.span)?;
        if value.ty != expected {
            return Err(invalid_hir(expression.span));
        }
        Ok(value)
    }

    fn lower_object_expression(
        &mut self,
        expression: &HirExpression,
    ) -> Result<LoweredObject, FrontendFailure> {
        let access = self
            .types
            .aggregate_access(&self.memory, expression.ty, expression.span)?
            .ok_or_else(|| invalid_hir(expression.span))?;
        match &expression.kind {
            HirExpressionKind::TupleConstructor { elements } => {
                let destination = self.expression_object_temporary(expression, access)?;
                let Some(HirTypeKind::Tuple(types)) = self.hir.type_kind(expression.ty) else {
                    return Err(invalid_hir(expression.span));
                };
                if elements.len() != types.len() {
                    return Err(invalid_hir(expression.span));
                }
                for (index, (element, expected)) in elements.iter().zip(types).enumerate() {
                    if !self.hir.types_compatible(element.ty, *expected) {
                        return Err(invalid_hir(element.span));
                    }
                    let index = u64::try_from(index).map_err(|_| invalid_hir(element.span))?;
                    let child = self.tuple_element_object(destination, index, element.span)?;
                    self.lower_constructor_operand(child, element)?;
                }
                self.finish_object_initialization(destination, expression.span)
            }
            HirExpressionKind::ArrayConstructor { elements } => {
                let destination = self.expression_object_temporary(expression, access)?;
                let Some(HirTypeKind::Array { element, length }) =
                    self.hir.type_kind(expression.ty)
                else {
                    return Err(invalid_hir(expression.span));
                };
                if u64::try_from(elements.len()) != Ok(*length) {
                    return Err(invalid_hir(expression.span));
                }
                for (index, value) in elements.iter().enumerate() {
                    if !self.hir.types_compatible(value.ty, *element) {
                        return Err(invalid_hir(value.span));
                    }
                    let index = u64::try_from(index).map_err(|_| invalid_hir(value.span))?;
                    let child =
                        self.array_element_object(destination, index, *length, value.span)?;
                    self.lower_constructor_operand(child, value)?;
                }
                self.finish_object_initialization(destination, expression.span)
            }
            HirExpressionKind::ArrayRepeatConstructor { value, length } => {
                let destination = self.expression_object_temporary(expression, access)?;
                let Some(HirTypeKind::Array {
                    element,
                    length: expected_length,
                }) = self.hir.type_kind(expression.ty)
                else {
                    return Err(invalid_hir(expression.span));
                };
                if length != expected_length || value.ty != *element {
                    return Err(invalid_hir(expression.span));
                }
                if matches!(self.hir.type_kind(value.ty), Some(HirTypeKind::Unit)) {
                    return Err(invalid_hir(value.span));
                }
                if let Some(element_access) =
                    self.types
                        .aggregate_access(&self.memory, value.ty, value.span)?
                {
                    let source = self.lower_object_expression(value)?;
                    if source.access != element_access {
                        return Err(invalid_hir(value.span));
                    }
                    let cleanup = self.is_object_temporary(source, value.span)?;
                    for index in 0..*length {
                        let child =
                            self.array_element_object(destination, index, *length, value.span)?;
                        if child.access != source.access {
                            return Err(invalid_hir(value.span));
                        }
                        self.cfg.emit_assignment(
                            child.pointer,
                            child.permission,
                            child.access,
                            PendingAssignmentSource::Object {
                                pointer: source.pointer,
                                permission: source.permission,
                                mode: crate::VirObjectSourceMode::Copy,
                            },
                            DraftSourceIdentity::HirNode(value.id),
                            value.span,
                        )?;
                    }
                    if cleanup {
                        self.emit(
                            VirInstruction::ObjectDeinitialize {
                                pointer: source.pointer,
                                permission: source.permission,
                                access: source.access,
                            },
                            value.span,
                        )?;
                    }
                } else {
                    let source = self.lower_expression(value)?;
                    if source.permission.is_some() {
                        return Err(invalid_hir(value.span));
                    }
                    for index in 0..*length {
                        let child =
                            self.array_element_object(destination, index, *length, value.span)?;
                        self.cfg.emit_assignment(
                            child.pointer,
                            child.permission,
                            child.access,
                            PendingAssignmentSource::Scalar {
                                value: source.value,
                            },
                            DraftSourceIdentity::HirNode(value.id),
                            value.span,
                        )?;
                    }
                }
                self.finish_object_initialization(destination, expression.span)
            }
            HirExpressionKind::StructConstructor { fields } => {
                let destination = self.expression_object_temporary(expression, access)?;
                for initializer in fields {
                    let child = self.field_object(
                        destination,
                        initializer.field,
                        None,
                        initializer.value.span,
                    )?;
                    self.lower_constructor_operand(child, &initializer.value)?;
                }
                self.finish_object_initialization(destination, expression.span)
            }
            HirExpressionKind::EnumConstructor { variant, fields } => {
                let destination = self.expression_object_temporary(expression, access)?;
                self.emit(
                    VirInstruction::EnumSetDiscriminant {
                        pointer: destination.pointer,
                        permission: destination.permission,
                        access,
                        variant: self.memory.variant(*variant, expression.span)?,
                        mode: crate::VirObjectDestinationMode::Initialize,
                    },
                    expression.span,
                )?;
                for initializer in fields {
                    let child = self.field_object(
                        destination,
                        initializer.field,
                        Some(*variant),
                        initializer.value.span,
                    )?;
                    self.lower_constructor_operand(child, &initializer.value)?;
                }
                self.finish_object_initialization(destination, expression.span)
            }
            HirExpressionKind::Read { place, .. } => {
                let place = self.lower_place(place, HirPlaceAccess::Read, expression.span)?;
                self.object_from_place(place, access, expression.span)
            }
            HirExpressionKind::Call(call) => {
                let value = self
                    .lower_call(expression, call, expression.span)?
                    .ok_or_else(|| invalid_hir(expression.span))?;
                let VirType::Pointer {
                    access: value_access,
                } = value.ty
                else {
                    return Err(invalid_hir(expression.span));
                };
                if value_access != access {
                    return Err(invalid_hir(expression.span));
                }
                Ok(LoweredObject {
                    pointer: value.value,
                    permission: value
                        .permission
                        .ok_or_else(|| invalid_hir(expression.span))?,
                    access,
                    drop_flag: value.drop_flag,
                })
            }
            HirExpressionKind::Unit
            | HirExpressionKind::Integer(_)
            | HirExpressionKind::Bool(_)
            | HirExpressionKind::Compare { .. }
            | HirExpressionKind::PointerDistance { .. }
            | HirExpressionKind::WordAdd { .. }
            | HirExpressionKind::PointerOffset { .. }
            | HirExpressionKind::Allocate { .. }
            | HirExpressionKind::OwnerAddress { .. }
            | HirExpressionKind::Borrow { .. }
            | HirExpressionKind::RawAddress { .. } => Err(invalid_hir(expression.span)),
            HirExpressionKind::Length { .. } => Err(invalid_hir(expression.span)),
        }
    }

    fn expression_object_temporary(
        &self,
        expression: &HirExpression,
        access: crate::VirMemoryAccess,
    ) -> Result<LoweredObject, FrontendFailure> {
        let local = self
            .object_temporaries
            .iter()
            .find(|storage| storage.owner == expression.id)
            .map(|storage| storage.local)
            .ok_or_else(|| invalid_hir(expression.span))?;
        let storage = self.storage_object(local, expression.span)?;
        (storage.access == access)
            .then_some(storage)
            .ok_or_else(|| invalid_hir(expression.span))
    }

    fn finish_object_initialization(
        &mut self,
        object: LoweredObject,
        source_span: ByteSpan,
    ) -> Result<LoweredObject, FrontendFailure> {
        let Some(local) = self.object_storage_local(object) else {
            return Err(invalid_hir(source_span));
        };
        if object.drop_flag.is_some() {
            self.set_local_drop_flag(local, true, source_span)?;
        }
        self.storage_object(local, source_span)
    }

    fn lower_constructor_operand(
        &mut self,
        destination: LoweredObject,
        value: &HirExpression,
    ) -> Result<(), FrontendFailure> {
        if matches!(self.hir.type_kind(value.ty), Some(HirTypeKind::Unit)) {
            self.types.require_unit_layout(value.ty, value.span)?;
            if !matches!(value.kind, HirExpressionKind::Unit)
                || self.memory.access(value.ty, value.span)? != destination.access
            {
                return Err(invalid_hir(value.span));
            }
            return Ok(());
        }
        if let Some(access) = self
            .types
            .aggregate_access(&self.memory, value.ty, value.span)?
        {
            if destination.access != access {
                return Err(invalid_hir(value.span));
            }
            let source = self.lower_object_expression(value)?;
            self.emit_object_assignment(
                destination,
                source,
                object_source_mode(value)?,
                DraftSourceIdentity::HirNode(value.id),
                value.span,
            )
        } else {
            let source_span = value.span;
            let source_type = value.ty;
            let source_identity = DraftSourceIdentity::HirNode(value.id);
            let value = self.lower_expression(value)?;
            if matches!(
                self.hir.type_kind(source_type),
                Some(HirTypeKind::Own { .. } | HirTypeKind::Reference { .. })
            ) {
                let value_permission = value.permission.ok_or_else(|| invalid_hir(source_span))?;
                self.emit(
                    VirInstruction::ResourceInitialize {
                        destination: destination.pointer,
                        destination_permission: destination.permission,
                        value: value.value,
                        value_permission,
                        access: destination.access,
                    },
                    source_span,
                )?;
                return Ok(());
            }
            if value.permission.is_some() {
                return Err(invalid_hir(source_span));
            }
            self.cfg.emit_assignment(
                destination.pointer,
                destination.permission,
                destination.access,
                PendingAssignmentSource::Scalar { value: value.value },
                source_identity,
                source_span,
            )
        }
    }

    /// Snapshot every source leaf before any destination write. Padding is
    /// deliberately absent, and a partial RHS (including self-copy) still
    /// generates real Load obligations. No destination initialization fact is
    /// assumed: the post-CFG scalar planner chooses Initialize/Store/Write.
    fn emit_plain_object_assignment(
        &mut self,
        destination: LoweredObject,
        source: LoweredObject,
        source_identity: DraftSourceIdentity,
        span: ByteSpan,
    ) -> Result<bool, FrontendFailure> {
        let shape = self
            .memory
            .schema()
            .object_shape(source.access)
            .map_err(|_| invalid_hir(span))?;
        if !shape.supports_storage_reset() {
            return Ok(false);
        }
        if destination.access != source.access {
            return Err(invalid_hir(span));
        }
        let mut values = Vec::with_capacity(shape.leaves().len());
        for leaf in shape.leaves() {
            let access = leaf.access();
            let ty = match self.memory.schema().ty(access.ty).map(|ty| &ty.kind) {
                Some(VirMemoryTypeKind::Bool) => VirType::Bool,
                Some(VirMemoryTypeKind::Integer(
                    crate::VirIntegerType::U64 | crate::VirIntegerType::Usize,
                )) => VirType::U64,
                _ => return Err(invalid_hir(span)),
            };
            let pointer = self.fresh_value(VirType::Pointer { access }, span)?;
            self.emit(
                VirInstruction::ObjectLeafAddress {
                    result: pointer,
                    base: source.pointer,
                    owner: source.access,
                    leaf: access,
                    offset_bytes: leaf.bytes().start_bytes(),
                },
                span,
            )?;
            let value = self.fresh_value(ty, span)?;
            self.emit(
                VirInstruction::Load {
                    result: value,
                    pointer: pointer.id,
                    permission: source.permission,
                    access,
                },
                span,
            )?;
            values.push((leaf.clone(), value));
        }
        if destination.pointer != source.pointer || destination.permission != source.permission {
            for (leaf, value) in values {
                let access = leaf.access();
                let pointer = self.fresh_value(VirType::Pointer { access }, span)?;
                self.emit(
                    VirInstruction::ObjectLeafAddress {
                        result: pointer,
                        base: destination.pointer,
                        owner: destination.access,
                        leaf: access,
                        offset_bytes: leaf.bytes().start_bytes(),
                    },
                    span,
                )?;
                self.cfg.emit_assignment(
                    pointer.id,
                    destination.permission,
                    access,
                    PendingAssignmentSource::Scalar { value: value.id },
                    source_identity,
                    span,
                )?;
            }
        }
        self.cleanup_object_temporary(source, source_identity, span)?;
        Ok(true)
    }

    fn emit_object_assignment(
        &mut self,
        destination: LoweredObject,
        source: LoweredObject,
        source_mode: crate::VirObjectSourceMode,
        source_identity: DraftSourceIdentity,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if destination.access != source.access {
            return Err(invalid_hir(source_span));
        }
        if destination.pointer == source.pointer && destination.permission == source.permission {
            if source_mode == crate::VirObjectSourceMode::Copy
                && self.emit_plain_object_assignment(
                    destination,
                    source,
                    source_identity,
                    source_span,
                )?
            {
                return Ok(());
            }
            return (source_mode == crate::VirObjectSourceMode::Copy)
                .then_some(())
                .ok_or_else(|| invalid_hir(source_span));
        }
        if let Some(condition) = destination.drop_flag
            && self.known_drop_flags.get(&condition) != Some(&false)
        {
            self.cfg.emit_cleanup(
                PendingCleanupKind::Object {
                    condition: Some(condition),
                },
                DraftObjectIdentity {
                    pointer: destination.pointer,
                    permission: destination.permission,
                    access: destination.access,
                },
                source_identity,
                source_span,
            )?;
            self.set_object_drop_flag(destination, false, source_span)?;
        }
        let cleanup_temporary = self.is_object_temporary(source, source_span)?;
        self.cfg.emit_assignment(
            destination.pointer,
            destination.permission,
            destination.access,
            PendingAssignmentSource::Object {
                pointer: source.pointer,
                permission: source.permission,
                mode: source_mode,
            },
            source_identity,
            source_span,
        )?;
        if source_mode == crate::VirObjectSourceMode::Move && source.drop_flag.is_some() {
            self.set_object_drop_flag(source, false, source_span)?;
        }
        if destination.drop_flag.is_some() {
            self.set_object_drop_flag(destination, true, source_span)?;
        }
        if cleanup_temporary && source_mode == crate::VirObjectSourceMode::Copy {
            if let Some(condition) = source.drop_flag {
                self.cfg.emit_cleanup(
                    PendingCleanupKind::Object {
                        condition: Some(condition),
                    },
                    DraftObjectIdentity {
                        pointer: source.pointer,
                        permission: source.permission,
                        access: source.access,
                    },
                    source_identity,
                    source_span,
                )?;
                self.set_object_drop_flag(source, false, source_span)?;
            } else {
                self.emit(
                    VirInstruction::ObjectDeinitialize {
                        pointer: source.pointer,
                        permission: source.permission,
                        access: source.access,
                    },
                    source_span,
                )?;
            }
        }
        Ok(())
    }

    fn object_storage_local(&self, object: LoweredObject) -> Option<HirLocalId> {
        (0..self.environment.len()).find_map(|index| {
            let raw = u32::try_from(index).ok()?;
            let local = HirLocalId::new(raw);
            let value = self.environment.optional(local)?;
            (value.value == object.pointer
                && value.permission == Some(object.permission)
                && value.ty
                    == (VirType::Pointer {
                        access: object.access,
                    }))
            .then_some(local)
        })
    }

    fn set_object_drop_flag(
        &mut self,
        object: LoweredObject,
        initialized: bool,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let local = self
            .object_storage_local(object)
            .ok_or_else(|| invalid_hir(source_span))?;
        self.set_local_drop_flag(local, initialized, source_span)
    }

    fn is_object_temporary(
        &self,
        object: LoweredObject,
        source_span: ByteSpan,
    ) -> Result<bool, FrontendFailure> {
        for constructor in &self.object_temporaries {
            let temporary = self.storage_object(constructor.local, source_span)?;
            if temporary.pointer == object.pointer
                && temporary.permission == object.permission
                && temporary.access == object.access
            {
                return Ok(true);
            }
        }
        for storage in &self.abi_call_storage {
            if storage.role != AbiCallStorageRole::Result {
                continue;
            }
            let temporary = self.storage_object(storage.local, source_span)?;
            if temporary.pointer == object.pointer
                && temporary.permission == object.permission
                && temporary.access == object.access
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn object_from_place(
        &self,
        place: LoweredPlace,
        access: crate::VirMemoryAccess,
        source_span: ByteSpan,
    ) -> Result<LoweredObject, FrontendFailure> {
        match place {
            LoweredPlace::Local(local) => self.local_object(local, source_span),
            LoweredPlace::Address(address) => {
                if self.memory.access(address.ty, source_span)? != access {
                    return Err(invalid_hir(source_span));
                }
                Ok(LoweredObject {
                    pointer: address.pointer,
                    permission: address.permission,
                    access,
                    drop_flag: None,
                })
            }
            LoweredPlace::Slice(_) => Err(invalid_hir(source_span)),
        }
    }

    fn local_object(
        &self,
        local: HirLocalId,
        source_span: ByteSpan,
    ) -> Result<LoweredObject, FrontendFailure> {
        if !self.storage_locals.contains(&local) {
            return Err(invalid_hir(source_span));
        }
        self.storage_object(local, source_span)
    }

    fn storage_object(
        &self,
        local: HirLocalId,
        source_span: ByteSpan,
    ) -> Result<LoweredObject, FrontendFailure> {
        let value = self.lookup_local(local, source_span)?;
        let VirType::Pointer { access } = value.ty else {
            return Err(invalid_hir(source_span));
        };
        Ok(LoweredObject {
            pointer: value.value,
            permission: value.permission.ok_or_else(|| invalid_hir(source_span))?,
            access,
            drop_flag: value.drop_flag,
        })
    }

    fn tuple_element_object(
        &mut self,
        owner: LoweredObject,
        index: u64,
        source_span: ByteSpan,
    ) -> Result<LoweredObject, FrontendFailure> {
        let (element_access, offset_bytes) = self
            .memory
            .schema()
            .tuple_element_projection(owner.access, index)
            .ok_or_else(|| invalid_hir(source_span))?;
        let result = self.fresh_value(
            VirType::Pointer {
                access: element_access,
            },
            source_span,
        )?;
        self.emit(
            VirInstruction::TupleElementAddress {
                result,
                base: owner.pointer,
                index,
                owner: owner.access,
                element_access,
                offset_bytes,
            },
            source_span,
        )?;
        Ok(LoweredObject {
            pointer: result.id,
            permission: owner.permission,
            access: element_access,
            drop_flag: None,
        })
    }

    fn array_element_object(
        &mut self,
        owner: LoweredObject,
        index: u64,
        expected_length: u64,
        source_span: ByteSpan,
    ) -> Result<LoweredObject, FrontendFailure> {
        let Some(crate::VirMemoryTypeKind::Array { element, length }) =
            self.memory.schema().kind(owner.access.ty)
        else {
            return Err(invalid_hir(source_span));
        };
        let element = *element;
        let length = *length;
        if length != expected_length || index >= length {
            return Err(invalid_hir(source_span));
        }
        let element_access = self
            .memory
            .schema()
            .access(element)
            .ok_or_else(|| invalid_hir(source_span))?;
        let stride_bytes = self
            .memory
            .schema()
            .layout(element_access.layout)
            .ok_or_else(|| invalid_hir(source_span))?
            .size_bytes;
        let lowered_index = self.lower_integer(index, source_span)?;
        let result = self.fresh_value(
            VirType::Pointer {
                access: element_access,
            },
            source_span,
        )?;
        self.emit(
            VirInstruction::IndexAddress {
                result,
                base: owner.pointer,
                index: lowered_index.value,
                source: owner.access,
                element: element_access,
                stride_bytes,
                bounds: VirIndexBounds::Array { length },
            },
            source_span,
        )?;
        Ok(LoweredObject {
            pointer: result.id,
            permission: owner.permission,
            access: element_access,
            drop_flag: None,
        })
    }

    fn field_object(
        &mut self,
        owner: LoweredObject,
        field: super::hir::HirFieldId,
        variant: Option<super::hir::HirVariantId>,
        source_span: ByteSpan,
    ) -> Result<LoweredObject, FrontendFailure> {
        let definition = self
            .hir
            .field(field)
            .ok_or_else(|| invalid_hir(source_span))?;
        let layout = self
            .hir
            .layout_of(definition.owner)
            .ok_or_else(|| invalid_hir(source_span))?;
        let offset_bytes = if let Some(variant) = variant {
            let variants = layout
                .variants
                .as_ref()
                .ok_or_else(|| invalid_hir(source_span))?;
            let case = variants
                .cases
                .iter()
                .find(|case| case.variant == variant)
                .ok_or_else(|| invalid_hir(source_span))?;
            let field_offset = case
                .fields
                .iter()
                .find(|candidate| candidate.field == field)
                .ok_or_else(|| invalid_hir(source_span))?
                .offset_bytes;
            case.payload_offset_bytes
                .checked_add(field_offset)
                .ok_or_else(|| invalid_hir(source_span))?
        } else {
            layout
                .fields
                .iter()
                .find(|candidate| candidate.field == field)
                .ok_or_else(|| invalid_hir(source_span))?
                .offset_bytes
        };
        if self.memory.access(definition.owner, source_span)? != owner.access {
            return Err(invalid_hir(source_span));
        }
        let field_access = self.memory.access(definition.ty, source_span)?;
        let result = self.fresh_value(
            VirType::Pointer {
                access: field_access,
            },
            source_span,
        )?;
        self.emit(
            VirInstruction::FieldAddress {
                result,
                base: owner.pointer,
                field: self.memory.field(field, source_span)?,
                owner: owner.access,
                field_access,
                offset_bytes,
            },
            source_span,
        )?;
        Ok(LoweredObject {
            pointer: result.id,
            permission: owner.permission,
            access: field_access,
            drop_flag: None,
        })
    }

    fn lower_allocate(
        &mut self,
        element_type: HirTypeId,
        size_bytes: u64,
        alignment: u64,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let access = self
            .types
            .pointee_access(&self.memory, element_type, source_span)?;
        let size = self.lower_integer(size_bytes, source_span)?;
        let pointer = self.fresh_value(VirType::Pointer { access }, source_span)?;
        let permission = self.fresh_value(VirType::Permission, source_span)?;
        self.emit(
            VirInstruction::Allocate {
                pointer_result: pointer,
                permission_result: permission,
                size_bytes: size.value,
                alignment,
                region: CORE0_REGION,
                element: access,
            },
            source_span,
        )?;
        let drop_flag = self.lower_generated_drop_flag(true, source_span)?;
        Ok(LoweredValue {
            value: pointer.id,
            ty: pointer.ty,
            metadata: None,
            permission: Some(permission.id),
            drop_flag: Some(drop_flag),
            loan: None,
        })
    }

    fn lower_raw_address(
        &mut self,
        place: &HirPlace,
        mutability: super::hir::HirMutability,
        raw_type: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let access = if mutability == super::hir::HirMutability::Mutable {
            HirPlaceAccess::Write
        } else {
            HirPlaceAccess::Read
        };
        let resolved = self
            .hir
            .resolve_place(self.function.id, place, access)
            .map_err(|_| invalid_hir(source_span))?;
        if self.hir.type_kind(raw_type)
            != Some(&HirTypeKind::RawPointer {
                pointee: resolved.ty,
                mutability,
            })
            || matches!(
                self.hir.type_kind(resolved.base_type),
                Some(HirTypeKind::RawPointer { .. })
            )
            || (resolved.projections.is_empty()
                && matches!(
                    self.hir.type_kind(resolved.base_type),
                    Some(HirTypeKind::Own { .. } | HirTypeKind::Reference { .. })
                ))
        {
            return Err(invalid_hir(source_span));
        }
        self.types.require_pointer(raw_type, source_span)?;
        let address = if resolved.projections.is_empty() {
            let HirPlaceBase::Local(local) = resolved.base;
            let storage = self.storage_object(local, source_span)?;
            LoweredAddress {
                pointer: storage.pointer,
                permission: storage.permission,
                metadata: None,
                ty: resolved.ty,
            }
        } else {
            match self.lower_place(place, access, source_span)? {
                LoweredPlace::Address(address) if address.metadata.is_none() => address,
                _ => return Err(invalid_hir(source_span)),
            }
        };
        let result = self.fresh_value(
            VirType::Pointer {
                access: self.memory.access(resolved.ty, source_span)?,
            },
            source_span,
        )?;
        self.emit(
            VirInstruction::RawAddress {
                result,
                base: address.pointer,
                source_permission: address.permission,
                raw_type: self.memory.access(raw_type, source_span)?,
            },
            source_span,
        )?;
        Ok(LoweredValue {
            value: result.id,
            ty: result.ty,
            metadata: None,
            permission: None,
            drop_flag: None,
            loan: None,
        })
    }

    fn lower_borrow(
        &mut self,
        place: &HirPlace,
        mutability: super::hir::HirMutability,
        region: super::hir::HirRegionId,
        reference_type: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let place_access = if mutability == super::hir::HirMutability::Mutable {
            HirPlaceAccess::Write
        } else {
            HirPlaceAccess::Read
        };
        let resolved = self
            .hir
            .resolve_place(self.function.id, place, place_access)
            .map_err(|_| invalid_hir(source_span))?;
        if matches!(
            self.hir.type_kind(resolved.ty),
            Some(HirTypeKind::Slice { .. })
        ) {
            return self.lower_slice_borrow(
                &resolved,
                mutability,
                region,
                reference_type,
                source_span,
            );
        }
        let HirPlaceBase::Local(base_local) = resolved.base;
        let parent = if matches!(
            resolved
                .projections
                .first()
                .map(|projection| &projection.kind),
            Some(ResolvedHirProjectionKind::Dereference { .. })
        ) && matches!(
            self.hir.type_kind(resolved.base_type),
            Some(HirTypeKind::Reference { .. })
        ) {
            match self
                .lookup_local(base_local, source_span)?
                .loan
                .ok_or_else(|| invalid_hir(source_span))?
            {
                LoweredLoan::Static(metadata) => Some(metadata),
                LoweredLoan::Authority { .. } | LoweredLoan::ConditionalAuthority { .. } => {
                    let address = match self.lower_place(place, place_access, source_span)? {
                        LoweredPlace::Address(address) => address,
                        _ => return Err(invalid_hir(source_span)),
                    };
                    let reference = self.memory.access(reference_type, source_span)?;
                    return self.lower_authority_reborrow(address, reference, region, source_span);
                }
            }
        } else {
            None
        };
        let (relative_start, relative_last_start) = loan_candidate_start_bounds(&resolved)?;
        let start_bytes = match parent {
            Some(parent) => parent
                .range
                .start_bytes
                .checked_add(relative_start)
                .ok_or_else(|| invalid_hir(source_span))?,
            None => relative_start,
        };
        let pointee = self.memory.access(resolved.ty, source_span)?;
        let size_bytes = self
            .memory
            .schema()
            .layout(pointee.layout)
            .map(|layout| layout.size_bytes)
            .ok_or_else(|| invalid_hir(source_span))?;
        let range = VirLoanRange {
            start_bytes,
            end_bytes: match parent {
                Some(parent) => parent.range.start_bytes.checked_add(relative_last_start),
                None => Some(relative_last_start),
            }
            .and_then(|last_start| last_start.checked_add(size_bytes))
            .ok_or_else(|| invalid_hir(source_span))?,
        };
        if parent.is_some_and(|parent| !parent.range.contains(range)) {
            return Err(invalid_hir(source_span));
        }
        let address = if resolved.projections.is_empty() {
            let HirPlaceBase::Local(local) = resolved.base;
            let storage = self.storage_object(local, source_span)?;
            LoweredAddress {
                pointer: storage.pointer,
                permission: storage.permission,
                metadata: None,
                ty: resolved.ty,
            }
        } else {
            match self.lower_place(place, place_access, source_span)? {
                LoweredPlace::Address(address) => address,
                LoweredPlace::Local(_) | LoweredPlace::Slice(_) => {
                    return Err(invalid_hir(source_span));
                }
            }
        };
        if address.ty != resolved.ty
            || address.metadata.is_some()
            || address.pointer == address.permission
        {
            return Err(invalid_hir(source_span));
        }
        let reference = self.memory.access(reference_type, source_span)?;
        let loan = VirLoanId::new(self.next_loan);
        self.next_loan = self
            .next_loan
            .checked_add(1)
            .ok_or_else(|| FrontendFailure::elaboration(source_span, "too many local loans"))?;
        let metadata = LoweredLoanMetadata {
            id: loan,
            kind: if mutability == super::hir::HirMutability::Mutable {
                VirLoanKind::Mutable
            } else {
                VirLoanKind::Shared
            },
            region: vir_borrow_region_id(self.hir, region)
                .ok_or_else(|| invalid_hir(source_span))?,
            parent: parent.map(|parent| parent.id),
            reference,
            range,
        };
        let reference_result =
            self.fresh_value(VirType::Pointer { access: pointee }, source_span)?;
        let permission_result = self.fresh_value(VirType::Permission, source_span)?;
        self.emit_generated(
            if parent.is_some() {
                VirInstruction::LoanReborrow {
                    effect: loan_effect(metadata, address.pointer, address.permission),
                    reference_result,
                    permission_result,
                }
            } else {
                VirInstruction::LoanBegin {
                    effect: loan_effect(metadata, address.pointer, address.permission),
                    reference_result,
                    permission_result,
                }
            },
            source_span,
            VirGeneratedReason::LoanEffect,
        )?;
        Ok(LoweredValue {
            value: reference_result.id,
            ty: reference_result.ty,
            metadata: None,
            permission: Some(permission_result.id),
            drop_flag: None,
            loan: Some(LoweredLoan::Static(metadata)),
        })
    }

    fn lower_slice_borrow(
        &mut self,
        resolved: &ResolvedHirPlace<'_>,
        mutability: super::hir::HirMutability,
        region: super::hir::HirRegionId,
        reference_type: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let (last, prefix_projections) = resolved
            .projections
            .split_last()
            .ok_or_else(|| invalid_hir(source_span))?;
        let ResolvedHirProjectionKind::Slice {
            start,
            end,
            bounds,
            stride_bytes,
            mutability: slice_mutability,
        } = &last.kind
        else {
            return Err(invalid_hir(source_span));
        };
        if *slice_mutability != mutability
            || prefix_projections.iter().any(|projection| {
                matches!(projection.kind, ResolvedHirProjectionKind::Slice { .. })
            })
        {
            return Err(FrontendFailure::unsupported(
                source_span,
                "one borrow expression may create only one safe slice range",
            ));
        }

        let HirPlaceBase::Local(base_local) = resolved.base;
        let reborrows_reference = matches!(
            resolved
                .projections
                .first()
                .map(|projection| &projection.kind),
            Some(ResolvedHirProjectionKind::Dereference { .. })
        ) && matches!(
            self.hir.type_kind(resolved.base_type),
            Some(HirTypeKind::Reference { .. })
        );
        let mut authority_parent = false;
        let parent =
            if slice_view_type(self.hir, resolved.base_type).is_some() || reborrows_reference {
                match self
                    .lookup_local(base_local, source_span)?
                    .loan
                    .ok_or_else(|| invalid_hir(source_span))?
                {
                    LoweredLoan::Static(metadata) => Some(metadata),
                    LoweredLoan::Authority { .. } | LoweredLoan::ConditionalAuthority { .. } => {
                        authority_parent = true;
                        None
                    }
                }
            } else {
                None
            };

        let base = if prefix_projections.is_empty() {
            if slice_view_type(self.hir, resolved.base_type).is_some() {
                let value = self.lookup_local(base_local, source_span)?;
                LoweredAddress {
                    pointer: value.value,
                    permission: value.permission.ok_or_else(|| invalid_hir(source_span))?,
                    metadata: value.metadata,
                    ty: resolved.base_type,
                }
            } else {
                let storage = self.storage_object(base_local, source_span)?;
                LoweredAddress {
                    pointer: storage.pointer,
                    permission: storage.permission,
                    metadata: None,
                    ty: resolved.base_type,
                }
            }
        } else {
            let prefix = ResolvedHirPlace {
                base: resolved.base,
                base_type: resolved.base_type,
                projections: prefix_projections.to_vec(),
                ty: last.input_type,
                writable: resolved.writable,
                required_alignment: last.required_alignment,
                static_offset_bytes: last.static_offset_bytes,
                span: resolved.span,
            };
            self.preflight_address_path(&prefix, source_span)?;
            self.lower_address_path(base_local, &prefix, HirPlaceAccess::Read, source_span)?
        };
        if base.ty != last.input_type {
            return Err(invalid_hir(source_span));
        }

        let source = self.memory.access(last.input_type, last.span)?;
        let reference = self.memory.access(reference_type, source_span)?;
        let Some(VirMemoryTypeKind::Slice {
            element,
            mutability: vir_mutability,
        }) = self.memory.schema().kind(reference.ty)
        else {
            return Err(invalid_hir(source_span));
        };
        if (*vir_mutability == crate::VirMutability::Mutable)
            != (mutability == super::hir::HirMutability::Mutable)
        {
            return Err(invalid_hir(source_span));
        }
        let element = self
            .memory
            .schema()
            .access(*element)
            .ok_or_else(|| invalid_hir(source_span))?;
        let lowered_bounds = match bounds {
            HirBoundsSource::Array { length } => {
                if base.metadata.is_some() {
                    return Err(invalid_hir(source_span));
                }
                VirIndexBounds::Array { length: *length }
            }
            HirBoundsSource::Slice { slice_type } => {
                if *slice_type != last.input_type {
                    return Err(invalid_hir(source_span));
                }
                VirIndexBounds::Slice {
                    length: base.metadata.ok_or_else(|| invalid_hir(source_span))?,
                }
            }
        };
        let start_value = match start {
            Some(start) => self.lower_expression(start)?,
            None => self.lower_integer(0, last.span)?,
        };
        let end_value = match end {
            Some(end) => self.lower_expression(end)?,
            None => match lowered_bounds {
                VirIndexBounds::Array { length } => self.lower_integer(length, last.span)?,
                VirIndexBounds::Slice { length } => LoweredValue {
                    value: length,
                    ty: VirType::U64,
                    metadata: None,
                    permission: None,
                    drop_flag: None,
                    loan: None,
                },
            },
        };
        if start_value.ty != VirType::U64
            || start_value.permission.is_some()
            || end_value.ty != VirType::U64
            || end_value.permission.is_some()
        {
            return Err(invalid_hir(source_span));
        }
        let pointer = self.fresh_value(VirType::Pointer { access: element }, last.span)?;
        let length = self.fresh_value(VirType::U64, last.span)?;
        self.emit(
            VirInstruction::SliceAddress {
                pointer_result: pointer,
                length_result: length,
                base: base.pointer,
                start: start_value.value,
                end: end_value.value,
                source,
                slice: reference,
                element,
                stride_bytes: *stride_bytes,
                bounds: lowered_bounds,
            },
            last.span,
        )?;
        if authority_parent {
            return self.lower_authority_reborrow(
                LoweredAddress {
                    pointer: pointer.id,
                    permission: base.permission,
                    metadata: Some(length.id),
                    ty: resolved.ty,
                },
                reference,
                region,
                source_span,
            );
        }
        let range = slice_loan_range(resolved, prefix_projections, last, parent, *stride_bytes)?;
        let loan = VirLoanId::new(self.next_loan);
        self.next_loan = self
            .next_loan
            .checked_add(1)
            .ok_or_else(|| FrontendFailure::elaboration(source_span, "too many local loans"))?;
        let metadata = LoweredLoanMetadata {
            id: loan,
            kind: if mutability == super::hir::HirMutability::Mutable {
                VirLoanKind::Mutable
            } else {
                VirLoanKind::Shared
            },
            region: vir_borrow_region_id(self.hir, region)
                .ok_or_else(|| invalid_hir(source_span))?,
            parent: parent.map(|parent| parent.id),
            reference,
            range,
        };
        let reference_result = self.fresh_value(pointer.ty, source_span)?;
        let permission_result = self.fresh_value(VirType::Permission, source_span)?;
        self.emit_generated(
            if parent.is_some() {
                VirInstruction::LoanReborrow {
                    effect: loan_effect(metadata, pointer.id, base.permission),
                    reference_result,
                    permission_result,
                }
            } else {
                VirInstruction::LoanBegin {
                    effect: loan_effect(metadata, pointer.id, base.permission),
                    reference_result,
                    permission_result,
                }
            },
            source_span,
            VirGeneratedReason::LoanEffect,
        )?;
        Ok(LoweredValue {
            value: reference_result.id,
            ty: reference_result.ty,
            metadata: Some(length.id),
            permission: Some(permission_result.id),
            drop_flag: None,
            loan: Some(LoweredLoan::Static(metadata)),
        })
    }

    fn lower_authority_reborrow(
        &mut self,
        address: LoweredAddress,
        reference: crate::VirMemoryAccess,
        region: super::hir::HirRegionId,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let (pointee, kind) = match self.memory.schema().kind(reference.ty) {
            Some(VirMemoryTypeKind::Slice {
                element: pointee,
                mutability,
            })
            | Some(VirMemoryTypeKind::Pointer {
                pointee,
                mutability,
                ..
            }) => (
                *pointee,
                if *mutability == crate::VirMutability::Mutable {
                    VirLoanKind::Mutable
                } else {
                    VirLoanKind::Shared
                },
            ),
            _ => return Err(invalid_hir(source_span)),
        };
        let access = self
            .memory
            .schema()
            .access(pointee)
            .ok_or_else(|| invalid_hir(source_span))?;
        let loan = VirLoanId::new(self.next_loan);
        self.next_loan = self
            .next_loan
            .checked_add(1)
            .ok_or_else(|| invalid_hir(source_span))?;
        let reference_result = self.fresh_value(VirType::Pointer { access }, source_span)?;
        let permission_result = self.fresh_value(VirType::Permission, source_span)?;
        self.emit_generated(
            VirInstruction::LoanReborrowAuthority {
                loan,
                region: vir_borrow_region_id(self.hir, region)
                    .ok_or_else(|| invalid_hir(source_span))?,
                effect: loan_authority_effect(address.pointer, address.permission, reference),
                reference_result,
                permission_result,
            },
            source_span,
            VirGeneratedReason::LoanEffect,
        )?;
        Ok(LoweredValue {
            value: reference_result.id,
            ty: reference_result.ty,
            metadata: address.metadata,
            permission: Some(permission_result.id),
            drop_flag: None,
            loan: Some(LoweredLoan::Authority { kind, reference }),
        })
    }

    fn lower_read(
        &mut self,
        place: &HirPlace,
        mode: HirUseMode,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        match self.lower_place(place, HirPlaceAccess::Read, source_span)? {
            LoweredPlace::Local(local) => {
                let value = self.lookup_local(local, source_span)?;
                self.apply_local_use_mode(local, value, mode, source_span)
            }
            LoweredPlace::Address(address) => self.lower_address_read(address, mode, source_span),
            LoweredPlace::Slice(value) => self.apply_scalar_use_mode(*value, mode, source_span),
        }
    }

    fn lower_address_read(
        &mut self,
        address: LoweredAddress,
        mode: HirUseMode,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        match self.hir.type_kind(address.ty) {
            Some(HirTypeKind::Own { .. }) if mode == HirUseMode::Move => {
                self.lower_resource_take(address, source_span)
            }
            Some(HirTypeKind::Reference { mutability, .. }) => {
                let original = self.lower_resource_take(address, source_span)?;
                if mode == HirUseMode::Move {
                    return Ok(original);
                }
                if *mutability != super::hir::HirMutability::Const {
                    return Err(invalid_hir(source_span));
                }
                let permission = original
                    .permission
                    .ok_or_else(|| invalid_hir(source_span))?;
                let reference = match original.loan.ok_or_else(|| invalid_hir(source_span))? {
                    LoweredLoan::Authority { reference, .. }
                    | LoweredLoan::ConditionalAuthority { reference, .. } => reference,
                    LoweredLoan::Static(_) => return Err(invalid_hir(source_span)),
                };
                let reference_result = self.fresh_value(original.ty, source_span)?;
                let permission_result = self.fresh_value(VirType::Permission, source_span)?;
                self.emit_generated(
                    VirInstruction::LoanAliasAuthority {
                        effect: loan_authority_effect(original.value, permission, reference),
                        reference_result,
                        permission_result,
                    },
                    source_span,
                    VirGeneratedReason::LoanEffect,
                )?;
                self.emit(
                    VirInstruction::ResourceInitialize {
                        destination: address.pointer,
                        destination_permission: address.permission,
                        value: original.value,
                        value_permission: permission,
                        access: self.memory.access(address.ty, source_span)?,
                    },
                    source_span,
                )?;
                Ok(LoweredValue {
                    value: reference_result.id,
                    ty: reference_result.ty,
                    metadata: None,
                    permission: Some(permission_result.id),
                    drop_flag: None,
                    loan: Some(LoweredLoan::Authority {
                        kind: VirLoanKind::Shared,
                        reference,
                    }),
                })
            }
            _ => self.lower_load(address, source_span),
        }
    }

    fn apply_scalar_use_mode(
        &mut self,
        mut value: LoweredValue,
        mode: HirUseMode,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        if mode == HirUseMode::Move {
            let source = value.permission.ok_or_else(|| invalid_hir(source_span))?;
            let result = self.fresh_value(VirType::Permission, source_span)?;
            self.emit(
                VirInstruction::PermissionMove { result, source },
                source_span,
            )?;
            value.permission = Some(result.id);
        }
        Ok(value)
    }

    fn apply_local_use_mode(
        &mut self,
        local: HirLocalId,
        value: LoweredValue,
        mode: HirUseMode,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        if let Some(loan) = value.loan {
            return match (loan.kind(), mode) {
                (VirLoanKind::Shared, HirUseMode::Copy) => {
                    let permission = value.permission.ok_or_else(|| invalid_hir(source_span))?;
                    let reference_result = self.fresh_value(value.ty, source_span)?;
                    let permission_result = self.fresh_value(VirType::Permission, source_span)?;
                    let instruction = match loan {
                        LoweredLoan::Static(metadata) => VirInstruction::LoanAliasShared {
                            effect: loan_effect(metadata, value.value, permission),
                            reference_result,
                            permission_result,
                        },
                        LoweredLoan::Authority { reference, .. }
                        | LoweredLoan::ConditionalAuthority { reference, .. } => {
                            VirInstruction::LoanAliasAuthority {
                                effect: loan_authority_effect(value.value, permission, reference),
                                reference_result,
                                permission_result,
                            }
                        }
                    };
                    self.emit_generated(instruction, source_span, VirGeneratedReason::LoanEffect)?;
                    Ok(LoweredValue {
                        value: reference_result.id,
                        ty: reference_result.ty,
                        metadata: value.metadata,
                        permission: Some(permission_result.id),
                        drop_flag: None,
                        loan: Some(loan),
                    })
                }
                (VirLoanKind::Mutable, HirUseMode::Move) => {
                    let moved = self.apply_scalar_use_mode(value, mode, source_span)?;
                    self.environment.forget(&[local], source_span)?;
                    Ok(moved)
                }
                _ => Err(invalid_hir(source_span)),
            };
        }
        let moved = self.apply_scalar_use_mode(value, mode, source_span)?;
        if mode == HirUseMode::Move && value.drop_flag.is_some() {
            self.set_local_drop_flag(local, false, source_span)?;
        }
        Ok(moved)
    }

    fn lower_resource_take(
        &mut self,
        source: LoweredAddress,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let (drop_flag, loan) = match self.hir.type_kind(source.ty) {
            Some(HirTypeKind::Own { .. }) => (
                Some(self.lower_generated_drop_flag(true, source_span)?),
                None,
            ),
            Some(HirTypeKind::Reference { mutability, .. }) => {
                let reference = self.memory.access(source.ty, source_span)?;
                (
                    None,
                    Some(LoweredLoan::Authority {
                        kind: if *mutability == super::hir::HirMutability::Mutable {
                            VirLoanKind::Mutable
                        } else {
                            VirLoanKind::Shared
                        },
                        reference,
                    }),
                )
            }
            _ => return Err(invalid_hir(source_span)),
        };
        let result_type = self
            .types
            .value_type(&self.memory, source.ty, source_span)?;
        let pointer_result = self.fresh_value(result_type, source_span)?;
        let permission_result = self.fresh_value(VirType::Permission, source_span)?;
        self.emit(
            VirInstruction::ResourceTake {
                pointer_result,
                permission_result,
                source: source.pointer,
                source_permission: source.permission,
                access: self.memory.access(source.ty, source_span)?,
            },
            source_span,
        )?;
        Ok(LoweredValue {
            value: pointer_result.id,
            ty: pointer_result.ty,
            metadata: None,
            permission: Some(permission_result.id),
            drop_flag,
            loan,
        })
    }

    fn lower_assign(
        &mut self,
        destination: &HirPlace,
        value: &HirExpression,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        self.lower_assignment_effects(destination, value, source_span)?;
        let HirPlaceBase::Local(local) = destination.base;
        if self.storage_locals.contains(&local) {
            let object = self.local_object(local, source_span)?;
            if object.drop_flag.is_some() {
                self.set_object_drop_flag(object, true, source_span)?;
            }
        }
        Ok(())
    }

    fn lower_assignment_effects(
        &mut self,
        destination: &HirPlace,
        value: &HirExpression,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if !self.hir.types_compatible(value.ty, destination.ty) {
            return Err(invalid_hir(source_span));
        }
        // Place evaluation, including each dynamic index operand, precedes RHS
        // evaluation. `lower_place` materializes that ordering exactly once.
        let lowered_destination =
            self.lower_place(destination, HirPlaceAccess::Write, source_span)?;
        if let Some(access) =
            self.types
                .aggregate_access(&self.memory, destination.ty, source_span)?
        {
            let destination = self.object_from_place(lowered_destination, access, source_span)?;
            let source = self.lower_object_expression(value)?;
            if self.emit_resource_object_assignment(destination, source, value, source_span)? {
                return Ok(());
            }
            if self.emit_plain_object_assignment(
                destination,
                source,
                DraftSourceIdentity::HirNode(value.id),
                source_span,
            )? {
                return Ok(());
            }
            return self.emit_object_assignment(
                destination,
                source,
                object_source_mode(value)?,
                DraftSourceIdentity::HirNode(value.id),
                source_span,
            );
        }

        if matches!(
            self.hir.type_kind(destination.ty),
            Some(HirTypeKind::RawPointer { .. })
        ) {
            let LoweredPlace::Local(local) = lowered_destination else {
                return Err(FrontendFailure::unsupported(
                    source_span,
                    "raw-pointer-bearing storage remains gated",
                ));
            };
            let replacement = self.lower_expression(value)?;
            if replacement.permission.is_some() || replacement.loan.is_some() {
                return Err(FrontendFailure::unsupported(
                    source_span,
                    "mutable raw bindings require authority-free addresses",
                ));
            }
            if self.local_types.get(local.index()) != Some(&replacement.ty) {
                return Err(invalid_hir(source_span));
            }
            return self.environment.reassign(local, replacement, source_span);
        }

        if let Some(HirTypeKind::Own { .. } | HirTypeKind::Reference { .. }) =
            self.hir.type_kind(destination.ty)
        {
            let LoweredPlace::Address(address) = lowered_destination else {
                return Err(invalid_hir(source_span));
            };
            let replacement = self.lower_expression(value)?;
            let replacement_permission = replacement
                .permission
                .ok_or_else(|| invalid_hir(source_span))?;
            // Evaluate/take the RHS before retiring the addressed destination.
            // ObjectDrop checks canonical present/moved payload state itself:
            // a moved leaf is skipped, a present leaf is dropped exactly once.
            let condition = self.lower_generated_drop_flag(true, source_span)?;
            self.cfg.emit_cleanup(
                PendingCleanupKind::Object {
                    condition: Some(condition),
                },
                DraftObjectIdentity {
                    pointer: address.pointer,
                    permission: address.permission,
                    access: self.memory.access(destination.ty, source_span)?,
                },
                DraftSourceIdentity::HirNode(destination.id),
                source_span,
            )?;
            return self.emit(
                VirInstruction::ResourceInitialize {
                    destination: address.pointer,
                    destination_permission: address.permission,
                    value: replacement.value,
                    value_permission: replacement_permission,
                    access: self.memory.access(destination.ty, source_span)?,
                },
                source_span,
            );
        }

        let scalar_type = self
            .types
            .value_type(&self.memory, destination.ty, source_span)?;
        if !matches!(scalar_type, VirType::U64 | VirType::Bool) {
            return Err(invalid_hir(source_span));
        }
        let value = self.lower_expression(value)?;
        if value.ty != scalar_type || value.permission.is_some() {
            return Err(invalid_hir(source_span));
        }
        match lowered_destination {
            LoweredPlace::Local(local) => self.reassign_local(local, value, source_span),
            LoweredPlace::Address(address) => self.cfg.emit_assignment(
                address.pointer,
                address.permission,
                self.memory.access(address.ty, source_span)?,
                PendingAssignmentSource::Scalar { value: value.value },
                DraftSourceIdentity::HirNode(destination.id),
                source_span,
            ),
            LoweredPlace::Slice(_) => Err(invalid_hir(source_span)),
        }
    }

    fn lower_place(
        &mut self,
        place: &HirPlace,
        access: HirPlaceAccess,
        source_span: ByteSpan,
    ) -> Result<LoweredPlace, FrontendFailure> {
        let resolved = self
            .hir
            .resolve_place(self.function.id, place, access)
            .map_err(|_| invalid_hir(source_span))?;
        let HirPlaceBase::Local(local) = resolved.base;
        if resolved.projections.is_empty() {
            if self.storage_locals.contains(&local)
                && self
                    .types
                    .aggregate_access(&self.memory, resolved.ty, source_span)?
                    .is_none()
            {
                let storage = self.storage_object(local, source_span)?;
                return Ok(LoweredPlace::Address(LoweredAddress {
                    pointer: storage.pointer,
                    permission: storage.permission,
                    metadata: None,
                    ty: resolved.ty,
                }));
            }
            return Ok(LoweredPlace::Local(local));
        }
        self.preflight_address_path(&resolved, source_span)?;
        let address = self.lower_address_path(local, &resolved, access, source_span)?;
        if let Some(length) = address.metadata {
            let Some(VirMemoryTypeKind::Slice { element, .. }) = self
                .memory
                .schema()
                .kind(self.memory.access(address.ty, source_span)?.ty)
            else {
                return Err(invalid_hir(source_span));
            };
            let element = self
                .memory
                .schema()
                .access(*element)
                .ok_or_else(|| invalid_hir(source_span))?;
            Ok(LoweredPlace::Slice(Box::new(LoweredValue {
                value: address.pointer,
                ty: VirType::Pointer { access: element },
                metadata: Some(length),
                permission: Some(address.permission),
                drop_flag: None,
                loan: None,
            })))
        } else {
            Ok(LoweredPlace::Address(address))
        }
    }

    fn preflight_address_path(
        &self,
        resolved: &ResolvedHirPlace<'_>,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let first = resolved
            .projections
            .first()
            .ok_or_else(|| invalid_hir(source_span))?;
        let HirPlaceBase::Local(base) = resolved.base;
        let starts_at_storage = self.storage_locals.contains(&base)
            && !matches!(&first.kind, ResolvedHirProjectionKind::Dereference { .. });
        let starts_at_slice = slice_view_type(self.hir, resolved.base_type).is_some();
        if !starts_at_storage
            && !starts_at_slice
            && !matches!(&first.kind, ResolvedHirProjectionKind::Dereference { .. })
        {
            return Err(invalid_hir(first.span));
        }
        for (index, projection) in resolved.projections.iter().enumerate() {
            match &projection.kind {
                ResolvedHirProjectionKind::Dereference { .. }
                    if index == 0 && !starts_at_storage && !starts_at_slice => {}
                ResolvedHirProjectionKind::Field { .. }
                | ResolvedHirProjectionKind::TupleElement { .. } => {}
                ResolvedHirProjectionKind::Downcast { .. }
                    if matches!(
                        resolved
                            .projections
                            .get(index + 1)
                            .map(|projection| &projection.kind),
                        Some(ResolvedHirProjectionKind::Field { .. })
                    ) => {}
                ResolvedHirProjectionKind::ConstantIndex { bounds, .. }
                | ResolvedHirProjectionKind::DynamicIndex { bounds, .. }
                    if matches!(
                        bounds,
                        HirBoundsSource::Array { .. } | HirBoundsSource::Slice { .. }
                    ) => {}
                ResolvedHirProjectionKind::Slice { .. } => {}
                ResolvedHirProjectionKind::Dereference { .. }
                | ResolvedHirProjectionKind::ConstantIndex { .. }
                | ResolvedHirProjectionKind::DynamicIndex { .. }
                | ResolvedHirProjectionKind::Downcast { .. } => {
                    // Pointer-valued loads still require a resource transfer
                    // representation outside this place path.
                    return Err(invalid_hir(projection.span));
                }
            }
        }
        Ok(())
    }

    fn lower_address_path(
        &mut self,
        local: HirLocalId,
        resolved: &ResolvedHirPlace<'_>,
        access: HirPlaceAccess,
        source_span: ByteSpan,
    ) -> Result<LoweredAddress, FrontendFailure> {
        let base = self.lookup_local(local, source_span)?;
        if !matches!(base.ty, VirType::Pointer { .. }) {
            return Err(invalid_hir(source_span));
        }
        let starts_at_storage = self.storage_locals.contains(&local)
            && !matches!(
                resolved
                    .projections
                    .first()
                    .map(|projection| &projection.kind),
                Some(ResolvedHirProjectionKind::Dereference { .. })
            );
        let starts_at_slice = slice_view_type(self.hir, resolved.base_type).is_some();
        let base_pointee = if starts_at_storage {
            let expected = self.memory.access(resolved.base_type, source_span)?;
            if base.ty != (VirType::Pointer { access: expected }) {
                return Err(invalid_hir(source_span));
            }
            None
        } else if starts_at_slice {
            None
        } else {
            Some(match access {
                HirPlaceAccess::Read => self
                    .types
                    .require_pointer(resolved.base_type, source_span)?,
                HirPlaceAccess::Write => self
                    .types
                    .require_writable_pointer(resolved.base_type, source_span)?,
            })
        };
        let mut permission = base.permission.ok_or_else(|| FrontendFailure::unsupported(source_span,
            "raw address has no access permission; dereference requires independently established authority"))?;
        let mut pointer = base.value;
        let mut current_type = resolved.base_type;
        let mut payload_offset = None;
        let mut slice_length = base.metadata;

        for (index, projection) in resolved.projections.iter().enumerate() {
            if projection.input_type != current_type {
                return Err(invalid_hir(projection.span));
            }
            match &projection.kind {
                ResolvedHirProjectionKind::Dereference {
                    pointer_type,
                    pointee,
                } if index == 0
                    && *pointer_type == resolved.base_type
                    && Some(*pointee) == base_pointee =>
                {
                    current_type = *pointee;
                    slice_length = None;
                }
                ResolvedHirProjectionKind::Field {
                    field,
                    offset_bytes,
                } => {
                    let offset_bytes = payload_offset
                        .take()
                        .map_or(Some(*offset_bytes), |payload: u64| {
                            payload.checked_add(*offset_bytes)
                        })
                        .ok_or_else(|| invalid_hir(projection.span))?;
                    let result = self.fresh_address(projection.output_type, projection.span)?;
                    self.emit(
                        VirInstruction::FieldAddress {
                            result,
                            base: pointer,
                            field: self.memory.field(*field, projection.span)?,
                            owner: self.memory.access(current_type, projection.span)?,
                            field_access: self
                                .memory
                                .access(projection.output_type, projection.span)?,
                            offset_bytes,
                        },
                        projection.span,
                    )?;
                    pointer = result.id;
                    current_type = projection.output_type;
                    slice_length = None;
                }
                ResolvedHirProjectionKind::Downcast {
                    payload_offset_bytes,
                    ..
                } if payload_offset.is_none() => {
                    payload_offset = Some(*payload_offset_bytes);
                    current_type = projection.output_type;
                }
                ResolvedHirProjectionKind::TupleElement {
                    index,
                    offset_bytes,
                } => {
                    let result = self.fresh_address(projection.output_type, projection.span)?;
                    self.emit(
                        VirInstruction::TupleElementAddress {
                            result,
                            base: pointer,
                            index: *index,
                            owner: self.memory.access(current_type, projection.span)?,
                            element_access: self
                                .memory
                                .access(projection.output_type, projection.span)?,
                            offset_bytes: *offset_bytes,
                        },
                        projection.span,
                    )?;
                    pointer = result.id;
                    current_type = projection.output_type;
                    slice_length = None;
                }
                ResolvedHirProjectionKind::ConstantIndex {
                    index,
                    bounds: HirBoundsSource::Array { length },
                    stride_bytes,
                    ..
                } => {
                    let index = self.lower_integer(*index, projection.span)?;
                    let result = self.fresh_address(projection.output_type, projection.span)?;
                    self.emit(
                        VirInstruction::IndexAddress {
                            result,
                            base: pointer,
                            index: index.value,
                            source: self.memory.access(current_type, projection.span)?,
                            element: self
                                .memory
                                .access(projection.output_type, projection.span)?,
                            stride_bytes: *stride_bytes,
                            bounds: VirIndexBounds::Array { length: *length },
                        },
                        projection.span,
                    )?;
                    pointer = result.id;
                    current_type = projection.output_type;
                    slice_length = None;
                }
                ResolvedHirProjectionKind::DynamicIndex {
                    index,
                    bounds: HirBoundsSource::Array { length },
                    stride_bytes,
                } => {
                    // The operand is lowered exactly when its projection is
                    // reached, before the address instruction that consumes it.
                    let index = self.lower_expression(index)?;
                    if index.ty != VirType::U64 || index.permission.is_some() {
                        return Err(invalid_hir(projection.span));
                    }
                    let result = self.fresh_address(projection.output_type, projection.span)?;
                    self.emit(
                        VirInstruction::IndexAddress {
                            result,
                            base: pointer,
                            index: index.value,
                            source: self.memory.access(current_type, projection.span)?,
                            element: self
                                .memory
                                .access(projection.output_type, projection.span)?,
                            stride_bytes: *stride_bytes,
                            bounds: VirIndexBounds::Array { length: *length },
                        },
                        projection.span,
                    )?;
                    pointer = result.id;
                    current_type = projection.output_type;
                    slice_length = None;
                }
                ResolvedHirProjectionKind::ConstantIndex {
                    index,
                    bounds: HirBoundsSource::Slice { slice_type },
                    stride_bytes,
                    ..
                } => {
                    if *slice_type != current_type {
                        return Err(invalid_hir(projection.span));
                    }
                    let length = slice_length.ok_or_else(|| invalid_hir(projection.span))?;
                    let index = self.lower_integer(*index, projection.span)?;
                    let result = self.fresh_address(projection.output_type, projection.span)?;
                    self.emit(
                        VirInstruction::IndexAddress {
                            result,
                            base: pointer,
                            index: index.value,
                            source: self.memory.access(current_type, projection.span)?,
                            element: self
                                .memory
                                .access(projection.output_type, projection.span)?,
                            stride_bytes: *stride_bytes,
                            bounds: VirIndexBounds::Slice { length },
                        },
                        projection.span,
                    )?;
                    pointer = result.id;
                    current_type = projection.output_type;
                    slice_length = None;
                }
                ResolvedHirProjectionKind::DynamicIndex {
                    index,
                    bounds: HirBoundsSource::Slice { slice_type },
                    stride_bytes,
                } => {
                    if *slice_type != current_type {
                        return Err(invalid_hir(projection.span));
                    }
                    let length = slice_length.ok_or_else(|| invalid_hir(projection.span))?;
                    let index = self.lower_expression(index)?;
                    if index.ty != VirType::U64 || index.permission.is_some() {
                        return Err(invalid_hir(projection.span));
                    }
                    let result = self.fresh_address(projection.output_type, projection.span)?;
                    self.emit(
                        VirInstruction::IndexAddress {
                            result,
                            base: pointer,
                            index: index.value,
                            source: self.memory.access(current_type, projection.span)?,
                            element: self
                                .memory
                                .access(projection.output_type, projection.span)?,
                            stride_bytes: *stride_bytes,
                            bounds: VirIndexBounds::Slice { length },
                        },
                        projection.span,
                    )?;
                    pointer = result.id;
                    current_type = projection.output_type;
                    slice_length = None;
                }
                ResolvedHirProjectionKind::Slice {
                    start,
                    end,
                    bounds,
                    stride_bytes,
                    ..
                } => {
                    let source = self.memory.access(current_type, projection.span)?;
                    let slice = self
                        .memory
                        .access(projection.output_type, projection.span)?;
                    let Some(VirMemoryTypeKind::Slice { element, .. }) =
                        self.memory.schema().kind(slice.ty)
                    else {
                        return Err(invalid_hir(projection.span));
                    };
                    let element = self
                        .memory
                        .schema()
                        .access(*element)
                        .ok_or_else(|| invalid_hir(projection.span))?;
                    let lowered_bounds = match bounds {
                        HirBoundsSource::Array { length } => {
                            if slice_length.is_some() {
                                return Err(invalid_hir(projection.span));
                            }
                            VirIndexBounds::Array { length: *length }
                        }
                        HirBoundsSource::Slice { slice_type } => {
                            if *slice_type != current_type {
                                return Err(invalid_hir(projection.span));
                            }
                            VirIndexBounds::Slice {
                                length: slice_length.ok_or_else(|| invalid_hir(projection.span))?,
                            }
                        }
                    };
                    let start = match start {
                        Some(start) => self.lower_expression(start)?,
                        None => self.lower_integer(0, projection.span)?,
                    };
                    let end = match end {
                        Some(end) => self.lower_expression(end)?,
                        None => match lowered_bounds {
                            VirIndexBounds::Array { length } => {
                                self.lower_integer(length, projection.span)?
                            }
                            VirIndexBounds::Slice { length } => LoweredValue {
                                value: length,
                                metadata: None,
                                permission: None,
                                drop_flag: None,
                                ty: VirType::U64,
                                loan: None,
                            },
                        },
                    };
                    if start.ty != VirType::U64
                        || start.permission.is_some()
                        || end.ty != VirType::U64
                        || end.permission.is_some()
                    {
                        return Err(invalid_hir(projection.span));
                    }
                    let pointer_result =
                        self.fresh_value(VirType::Pointer { access: element }, projection.span)?;
                    let length_result = self.fresh_value(VirType::U64, projection.span)?;
                    let permission_result =
                        self.fresh_value(VirType::Permission, projection.span)?;
                    self.emit(
                        VirInstruction::SliceRange {
                            pointer_result,
                            length_result,
                            permission_result,
                            base: pointer,
                            permission,
                            start: start.value,
                            end: end.value,
                            source,
                            slice,
                            element,
                            stride_bytes: *stride_bytes,
                            bounds: lowered_bounds,
                        },
                        projection.span,
                    )?;
                    pointer = pointer_result.id;
                    permission = permission_result.id;
                    current_type = projection.output_type;
                    slice_length = Some(length_result.id);
                }
                _ => return Err(invalid_hir(projection.span)),
            }
            if current_type != projection.output_type {
                return Err(invalid_hir(projection.span));
            }
        }
        if current_type != resolved.ty {
            return Err(invalid_hir(source_span));
        }
        if payload_offset.is_some()
            || (slice_length.is_some() != slice_view_type(self.hir, current_type).is_some())
        {
            return Err(invalid_hir(source_span));
        }
        Ok(LoweredAddress {
            pointer,
            permission,
            metadata: slice_length,
            ty: current_type,
        })
    }

    fn fresh_address(
        &mut self,
        ty: HirTypeId,
        source_span: ByteSpan,
    ) -> Result<VirValue, FrontendFailure> {
        self.fresh_value(
            VirType::Pointer {
                access: self.memory.access(ty, source_span)?,
            },
            source_span,
        )
    }

    fn lower_load(
        &mut self,
        address: LoweredAddress,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let scalar_type = self
            .types
            .value_type(&self.memory, address.ty, source_span)?;
        if !matches!(scalar_type, VirType::U64 | VirType::Bool) {
            return Err(invalid_hir(source_span));
        }
        let result = self.fresh_value(scalar_type, source_span)?;
        self.emit(
            VirInstruction::Load {
                result,
                pointer: address.pointer,
                permission: address.permission,
                access: self.memory.access(address.ty, source_span)?,
            },
            source_span,
        )?;
        Ok(runtime_value(result))
    }

    fn lower_word_add(
        &mut self,
        operands: &[HirExpression],
        operation_spans: &[ByteSpan],
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let Some(first) = operands.first() else {
            return Err(invalid_hir(source_span));
        };
        if operands.len() < 2 || operation_spans.len() + 1 != operands.len() {
            return Err(invalid_hir(source_span));
        }
        let mut accumulated = self.lower_expression(first)?;
        if accumulated.ty != VirType::U64 || accumulated.permission.is_some() {
            return Err(invalid_hir(source_span));
        }
        for (right, operation_span) in operands[1..].iter().zip(operation_spans) {
            let right = self.lower_expression(right)?;
            if right.ty != VirType::U64 || right.permission.is_some() {
                return Err(invalid_hir(*operation_span));
            }
            let result = self.fresh_value(VirType::U64, *operation_span)?;
            self.emit(
                VirInstruction::WordAdd {
                    result,
                    left: accumulated.value,
                    right: right.value,
                },
                *operation_span,
            )?;
            accumulated = runtime_value(result);
        }
        Ok(accumulated)
    }

    fn lower_pointer_offset(
        &mut self,
        base: LoweredValue,
        delta_bytes: u64,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        if !matches!(base.ty, VirType::Pointer { .. }) {
            return Err(invalid_hir(source_span));
        }
        let delta = self.lower_integer(delta_bytes, source_span)?;
        let result = self.fresh_value(base.ty, source_span)?;
        self.emit(
            VirInstruction::PointerOffset {
                result,
                base: base.value,
                delta_bytes: delta.value,
            },
            source_span,
        )?;
        Ok(LoweredValue {
            value: result.id,
            ty: result.ty,
            metadata: None,
            permission: base.permission,
            drop_flag: None,
            loan: None,
        })
    }

    fn lower_integer(
        &mut self,
        word: u64,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let result = self.fresh_value(VirType::U64, source_span)?;
        self.emit(
            VirInstruction::Constant {
                result,
                value: VirConstant::U64(word),
            },
            source_span,
        )?;
        Ok(runtime_value(result))
    }

    fn lower_generated_integer(
        &mut self,
        word: u64,
        parent_span: ByteSpan,
        reason: VirGeneratedReason,
    ) -> Result<LoweredValue, FrontendFailure> {
        let result = self.fresh_value(VirType::U64, parent_span)?;
        self.emit_generated(
            VirInstruction::Constant {
                result,
                value: VirConstant::U64(word),
            },
            parent_span,
            reason,
        )?;
        Ok(runtime_value(result))
    }

    fn lower_bool(
        &mut self,
        value: bool,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        let result = self.fresh_value(VirType::Bool, source_span)?;
        self.emit(
            VirInstruction::Constant {
                result,
                value: VirConstant::Bool(value),
            },
            source_span,
        )?;
        Ok(runtime_value(result))
    }

    fn lower_generated_drop_flag(
        &mut self,
        value: bool,
        parent_span: ByteSpan,
    ) -> Result<VirValueId, FrontendFailure> {
        let result = self.fresh_value(VirType::Bool, parent_span)?;
        self.emit_generated(
            VirInstruction::Constant {
                result,
                value: VirConstant::Bool(value),
            },
            parent_span,
            VirGeneratedReason::ImplicitDrop,
        )?;
        self.known_drop_flags.insert(result.id, value);
        Ok(result.id)
    }

    fn initial_drop_flag(
        &mut self,
        ty: HirTypeId,
        initialized: bool,
        source_span: ByteSpan,
    ) -> Result<Option<VirValueId>, FrontendFailure> {
        let reference_cleanup = matches!(
            self.hir.type_kind(ty),
            Some(
                HirTypeKind::Array { .. }
                    | HirTypeKind::Tuple(_)
                    | HirTypeKind::Struct { .. }
                    | HirTypeKind::Enum { .. }
            )
        ) && self
            .memory
            .schema()
            .object_shape(self.memory.access(ty, source_span)?)
            .is_ok_and(|shape| {
                shape
                    .resource_leaves()
                    .iter()
                    .any(|leaf| leaf.kind() == crate::VirPointerKind::Reference)
            });
        match self.hir.type_capabilities(ty) {
            Some(capabilities)
                if capabilities.drop == crate::DropCapability::BuiltinDrop || reference_cleanup =>
            {
                self.lower_generated_drop_flag(initialized, source_span)
                    .map(Some)
            }
            Some(capabilities) if capabilities.drop == crate::DropCapability::TrivialDrop => {
                Ok(None)
            }
            _ => Err(invalid_hir(source_span)),
        }
    }

    fn initial_access_drop_flag(
        &mut self,
        access: crate::VirMemoryAccess,
        initialized: bool,
        source_span: ByteSpan,
    ) -> Result<Option<VirValueId>, FrontendFailure> {
        let reference_cleanup = self
            .memory
            .schema()
            .object_shape(access)
            .is_ok_and(|shape| {
                shape
                    .resource_leaves()
                    .iter()
                    .any(|leaf| leaf.kind() == crate::VirPointerKind::Reference)
            });
        match self.memory.schema().type_capabilities(access.ty) {
            Some(capabilities)
                if capabilities.drop == crate::DropCapability::BuiltinDrop || reference_cleanup =>
            {
                self.lower_generated_drop_flag(initialized, source_span)
                    .map(Some)
            }
            Some(capabilities) if capabilities.drop == crate::DropCapability::TrivialDrop => {
                Ok(None)
            }
            _ => Err(invalid_hir(source_span)),
        }
    }

    fn lower_condition(
        &mut self,
        expression: &HirExpression,
    ) -> Result<LoweredCondition, FrontendFailure> {
        if let HirExpressionKind::Compare {
            predicate,
            left,
            right,
            operation_span,
        } = &expression.kind
        {
            return self.lower_compare_with_facts(
                *predicate,
                left,
                right,
                *operation_span,
                expression.span,
            );
        }
        let value = self.lower_expression(expression)?;
        Ok(LoweredCondition {
            fact_values: vec![VirValue {
                id: value.value,
                ty: value.ty,
            }],
            value,
        })
    }

    fn lower_compare(
        &mut self,
        predicate: HirIntegerPredicate,
        left: &HirExpression,
        right: &HirExpression,
        operation_span: ByteSpan,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        self.lower_compare_with_facts(predicate, left, right, operation_span, source_span)
            .map(|condition| condition.value)
    }

    fn lower_compare_with_facts(
        &mut self,
        predicate: HirIntegerPredicate,
        left: &HirExpression,
        right: &HirExpression,
        operation_span: ByteSpan,
        source_span: ByteSpan,
    ) -> Result<LoweredCondition, FrontendFailure> {
        if self.types.matching_raw_pointers(left.ty, right.ty) {
            let left = self.lower_expression(left)?;
            let right = self.lower_expression(right)?;
            let result = self.fresh_value(VirType::Bool, source_span)?;
            self.emit(
                VirInstruction::PointerCompare {
                    result,
                    predicate: match predicate {
                        HirIntegerPredicate::Equal => VirIntegerPredicate::Equal,
                        HirIntegerPredicate::NotEqual => VirIntegerPredicate::NotEqual,
                        HirIntegerPredicate::LessThan => VirIntegerPredicate::LessThan,
                        HirIntegerPredicate::LessOrEqual => VirIntegerPredicate::LessOrEqual,
                        HirIntegerPredicate::GreaterThan => VirIntegerPredicate::GreaterThan,
                        HirIntegerPredicate::GreaterOrEqual => VirIntegerPredicate::GreaterOrEqual,
                    },
                    left: left.value,
                    right: right.value,
                },
                operation_span,
            )?;
            return Ok(LoweredCondition {
                value: runtime_value(result),
                fact_values: vec![result],
            });
        }
        self.types.require_runtime_word(left.ty, left.span)?;
        self.types.require_runtime_word(right.ty, right.span)?;
        if left.ty != right.ty {
            return Err(invalid_hir(operation_span));
        }
        let left = self.lower_expression(left)?;
        let right = self.lower_expression(right)?;
        if left.ty != VirType::U64
            || right.ty != VirType::U64
            || left.permission.is_some()
            || right.permission.is_some()
        {
            return Err(invalid_hir(operation_span));
        }
        let result = self.fresh_value(VirType::Bool, source_span)?;
        self.emit(
            VirInstruction::Compare {
                result,
                predicate: match predicate {
                    HirIntegerPredicate::Equal => VirIntegerPredicate::Equal,
                    HirIntegerPredicate::NotEqual => VirIntegerPredicate::NotEqual,
                    HirIntegerPredicate::LessThan => VirIntegerPredicate::LessThan,
                    HirIntegerPredicate::LessOrEqual => VirIntegerPredicate::LessOrEqual,
                    HirIntegerPredicate::GreaterThan => VirIntegerPredicate::GreaterThan,
                    HirIntegerPredicate::GreaterOrEqual => VirIntegerPredicate::GreaterOrEqual,
                },
                left: left.value,
                right: right.value,
            },
            operation_span,
        )?;
        Ok(LoweredCondition {
            value: runtime_value(result),
            fact_values: vec![
                VirValue {
                    id: left.value,
                    ty: left.ty,
                },
                VirValue {
                    id: right.value,
                    ty: right.ty,
                },
                result,
            ],
        })
    }

    fn emit_integer_compare(
        &mut self,
        predicate: VirIntegerPredicate,
        left: VirValue,
        right: VirValue,
        source_span: ByteSpan,
    ) -> Result<LoweredCondition, FrontendFailure> {
        if left.ty != VirType::U64 || right.ty != VirType::U64 {
            return Err(invalid_hir(source_span));
        }
        let result = self.fresh_value(VirType::Bool, source_span)?;
        self.emit(
            VirInstruction::Compare {
                result,
                predicate,
                left: left.id,
                right: right.id,
            },
            source_span,
        )?;
        Ok(LoweredCondition {
            value: runtime_value(result),
            fact_values: vec![left, right, result],
        })
    }

    fn assign_local(
        &mut self,
        local: HirLocalId,
        value: LoweredValue,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let expected = self
            .local_types
            .get(local.index())
            .copied()
            .ok_or_else(|| invalid_hir(source_span))?;
        if value.ty != expected {
            return Err(invalid_hir(source_span));
        }
        self.environment.initialize(local, value, source_span)
    }

    fn reassign_local(
        &mut self,
        local: HirLocalId,
        value: LoweredValue,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let expected = self
            .local_types
            .get(local.index())
            .copied()
            .ok_or_else(|| invalid_hir(source_span))?;
        if expected != VirType::U64 || value.ty != expected || value.permission.is_some() {
            return Err(invalid_hir(source_span));
        }
        self.environment.reassign(local, value, source_span)
    }

    fn set_local_drop_flag(
        &mut self,
        local: HirLocalId,
        initialized: bool,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let mut value = self.lookup_local(local, source_span)?;
        if value.drop_flag.is_none() {
            return Err(invalid_hir(source_span));
        }
        value.drop_flag = Some(self.lower_generated_drop_flag(initialized, source_span)?);
        self.environment.reassign(local, value, source_span)
    }

    fn local(
        &self,
        local: HirLocalId,
        source_span: ByteSpan,
    ) -> Result<&HirLocal, FrontendFailure> {
        self.function
            .body()
            .and_then(|body| body.locals.get(local.index()))
            .filter(|definition| definition.id == local)
            .ok_or_else(|| invalid_hir(source_span))
    }

    fn lookup_local(
        &self,
        local: HirLocalId,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        self.environment.lookup(local, source_span)
    }

    fn fresh_value(
        &mut self,
        ty: VirType,
        source_span: ByteSpan,
    ) -> Result<VirValue, FrontendFailure> {
        self.cfg.fresh_value(ty, source_span)
    }

    fn emit(
        &mut self,
        instruction: VirInstruction,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        self.cfg.emit(instruction, source_span)
    }

    fn emit_generated(
        &mut self,
        instruction: VirInstruction,
        parent_span: ByteSpan,
        reason: VirGeneratedReason,
    ) -> Result<(), FrontendFailure> {
        self.cfg.emit_generated(instruction, parent_span, reason)
    }
}

fn runtime_value(value: VirValue) -> LoweredValue {
    LoweredValue {
        value: value.id,
        ty: value.ty,
        metadata: None,
        permission: None,
        drop_flag: None,
        loan: None,
    }
}

fn object_value(object: LoweredObject) -> LoweredValue {
    LoweredValue {
        value: object.pointer,
        ty: VirType::Pointer {
            access: object.access,
        },
        metadata: None,
        permission: Some(object.permission),
        drop_flag: object.drop_flag,
        loan: None,
    }
}

fn slice_view_type(
    program: &HirProgram,
    ty: HirTypeId,
) -> Option<(HirTypeId, super::hir::HirMutability)> {
    match program.type_kind(ty)? {
        HirTypeKind::Slice {
            element,
            mutability,
        } => Some((*element, *mutability)),
        HirTypeKind::Reference {
            pointee,
            mutability,
            ..
        } => match program.type_kind(*pointee)? {
            HirTypeKind::Slice { element, .. } => Some((*element, *mutability)),
            _ => None,
        },
        _ => None,
    }
}

fn slice_bound_constant(bound: Option<&HirExpression>, default: u64) -> Option<u64> {
    match bound {
        None => Some(default),
        Some(HirExpression {
            kind: HirExpressionKind::Integer(value),
            ..
        }) => Some(*value),
        Some(_) => None,
    }
}

fn slice_loan_range(
    _resolved: &ResolvedHirPlace<'_>,
    prefix: &[ResolvedHirProjection<'_>],
    projection: &ResolvedHirProjection<'_>,
    parent: Option<LoweredLoanMetadata>,
    stride_bytes: u64,
) -> Result<VirLoanRange, FrontendFailure> {
    if let Some(parent) = parent {
        return Ok(parent.range);
    }
    let ResolvedHirProjectionKind::Slice {
        start, end, bounds, ..
    } = &projection.kind
    else {
        return Err(invalid_hir(projection.span));
    };
    let HirBoundsSource::Array { length } = bounds else {
        return Err(invalid_hir(projection.span));
    };
    let (first_base, last_base) = projection_candidate_start_bounds(prefix)?;
    let full_end = length
        .checked_mul(stride_bytes)
        .and_then(|bytes| last_base.checked_add(bytes))
        .ok_or_else(|| invalid_hir(projection.span))?;
    let exact = slice_bound_constant(*start, 0).zip(slice_bound_constant(*end, *length));
    if let Some((start, end)) = exact {
        if start > end || end > *length {
            return Err(invalid_hir(projection.span));
        }
        return Ok(VirLoanRange {
            start_bytes: start
                .checked_mul(stride_bytes)
                .and_then(|bytes| first_base.checked_add(bytes))
                .ok_or_else(|| invalid_hir(projection.span))?,
            end_bytes: end
                .checked_mul(stride_bytes)
                .and_then(|bytes| last_base.checked_add(bytes))
                .ok_or_else(|| invalid_hir(projection.span))?,
        });
    }
    Ok(VirLoanRange {
        start_bytes: first_base,
        end_bytes: full_end,
    })
}

/// Returns the minimum and maximum allocation-relative start offsets selected
/// by a place. Dynamic fixed-array indices contribute their complete bounded
/// candidate set; slice bounds remain symbolic and are intentionally gated.
fn loan_candidate_start_bounds(
    place: &ResolvedHirPlace<'_>,
) -> Result<(u64, u64), FrontendFailure> {
    projection_candidate_start_bounds(&place.projections)
}

fn projection_candidate_start_bounds(
    projections: &[ResolvedHirProjection<'_>],
) -> Result<(u64, u64), FrontendFailure> {
    let mut first = 0_u64;
    let mut last = 0_u64;
    for projection in projections {
        let delta = match &projection.kind {
            ResolvedHirProjectionKind::Dereference { .. } => {
                first = 0;
                last = 0;
                continue;
            }
            ResolvedHirProjectionKind::Field { offset_bytes, .. }
            | ResolvedHirProjectionKind::TupleElement { offset_bytes, .. }
            | ResolvedHirProjectionKind::ConstantIndex { offset_bytes, .. } => *offset_bytes,
            ResolvedHirProjectionKind::Downcast {
                payload_offset_bytes,
                ..
            } => *payload_offset_bytes,
            ResolvedHirProjectionKind::DynamicIndex {
                bounds: HirBoundsSource::Array { length },
                stride_bytes,
                ..
            } => {
                let maximum = length
                    .checked_sub(1)
                    .and_then(|index| index.checked_mul(*stride_bytes))
                    .ok_or_else(|| invalid_hir(projection.span))?;
                last = last
                    .checked_add(maximum)
                    .ok_or_else(|| invalid_hir(projection.span))?;
                continue;
            }
            ResolvedHirProjectionKind::DynamicIndex {
                bounds: HirBoundsSource::Slice { .. },
                ..
            }
            | ResolvedHirProjectionKind::Slice { .. } => {
                return Err(FrontendFailure::unsupported(
                    projection.span,
                    "slice-index borrow ranges require the symbolic range solver from stage 7.4",
                ));
            }
        };
        first = first
            .checked_add(delta)
            .ok_or_else(|| invalid_hir(projection.span))?;
        last = last
            .checked_add(delta)
            .ok_or_else(|| invalid_hir(projection.span))?;
    }
    Ok((first, last))
}

fn loan_effect(
    loan: LoweredLoanMetadata,
    source_pointer: VirValueId,
    source_permission: VirValueId,
) -> VirLoanEffect {
    VirLoanEffect {
        loan: loan.id,
        kind: loan.kind,
        region: loan.region,
        parent: loan.parent,
        source_pointer,
        source_permission,
        reference: loan.reference,
        range: loan.range,
        // The canonical generated origin depends on the completed CFG location
        // table and is patched before the raw unit crosses validation.
        origin: VirOriginId::new(u32::MAX),
    }
}

fn loan_authority_effect(
    source_pointer: VirValueId,
    source_permission: VirValueId,
    reference: crate::VirMemoryAccess,
) -> crate::VirLoanAuthorityEffect {
    crate::VirLoanAuthorityEffect {
        source_pointer,
        source_permission,
        reference,
        origin: VirOriginId::new(u32::MAX),
    }
}

fn vir_object_source_mode(mode: HirUseMode) -> crate::VirObjectSourceMode {
    match mode {
        HirUseMode::Copy => crate::VirObjectSourceMode::Copy,
        HirUseMode::Move => crate::VirObjectSourceMode::Move,
    }
}

fn object_source_mode(
    expression: &HirExpression,
) -> Result<crate::VirObjectSourceMode, FrontendFailure> {
    match &expression.kind {
        HirExpressionKind::Read { mode, .. } => Ok(vir_object_source_mode(*mode)),
        HirExpressionKind::TupleConstructor { .. }
        | HirExpressionKind::ArrayConstructor { .. }
        | HirExpressionKind::ArrayRepeatConstructor { .. }
        | HirExpressionKind::StructConstructor { .. }
        | HirExpressionKind::EnumConstructor { .. }
        | HirExpressionKind::Call(_) => Ok(crate::VirObjectSourceMode::Move),
        _ => Err(invalid_hir(expression.span)),
    }
}

fn lowered_value_ids(value: LoweredValue) -> Vec<VirValueId> {
    let mut values = vec![value.value];
    if let Some(metadata) = value.metadata {
        values.push(metadata);
    }
    if let Some(permission) = value.permission {
        values.push(permission);
    }
    values
}

fn read_resource_local(expression: &HirExpression) -> Option<HirLocalId> {
    let HirExpressionKind::Read { place, .. } = &expression.kind else {
        return None;
    };
    let HirPlaceBase::Local(local) = place.base;
    Some(local)
}

fn extend_unique_facts(facts: &mut Vec<VirValue>, candidates: &[VirValue]) {
    for candidate in candidates {
        if facts.iter().all(|fact| fact.id != candidate.id) {
            facts.push(*candidate);
        }
    }
}

fn block_falls_through(block: &HirBlock) -> bool {
    block.statements.last().is_none_or(statement_falls_through)
}

fn statement_falls_through(statement: &HirStatement) -> bool {
    match &statement.kind {
        HirStatementKind::Return { .. }
        | HirStatementKind::Break { .. }
        | HirStatementKind::Continue { .. } => false,
        HirStatementKind::Block { block } => block_falls_through(block),
        HirStatementKind::If {
            then_block,
            else_block: Some(else_block),
            ..
        } => block_falls_through(then_block) || block_falls_through(else_block),
        HirStatementKind::Prove { .. }
        | HirStatementKind::Declare { .. }
        | HirStatementKind::Let { .. }
        | HirStatementKind::Assign { .. }
        | HirStatementKind::Free { .. }
        | HirStatementKind::Evaluate { .. }
        | HirStatementKind::If {
            else_block: None, ..
        }
        | HirStatementKind::While { .. }
        | HirStatementKind::For { .. } => true,
        HirStatementKind::Match { arms, .. } => {
            arms.iter().any(|arm| block_falls_through(&arm.body))
        }
    }
}

fn collect_addressable_storage_locals(block: &HirBlock) -> BTreeSet<HirLocalId> {
    let mut collector = AddressableStorageCollector::default();
    collector.visit_block(block);
    collector.locals
}

#[derive(Default)]
struct AddressableStorageCollector {
    locals: BTreeSet<HirLocalId>,
}

impl<'hir> HirVisitor<'hir> for AddressableStorageCollector {
    fn visit_statement(&mut self, statement: &'hir HirStatement) {
        if let HirStatementKind::Declare { local } = &statement.kind {
            self.locals.insert(*local);
        }
        walk_statement(self, statement);
    }

    fn visit_expression(&mut self, expression: &'hir HirExpression) {
        match &expression.kind {
            HirExpressionKind::Borrow { place, .. }
            | HirExpressionKind::RawAddress { place, .. }
                if !matches!(
                    place.projections.first().map(|projection| &projection.kind),
                    Some(HirProjectionKind::Dereference)
                ) =>
            {
                let HirPlaceBase::Local(local) = place.base;
                self.locals.insert(local);
            }
            _ => {}
        }
        walk_expression(self, expression);
    }
}

struct ConstructorCollector<'output, 'hir> {
    output: &'output mut Vec<&'hir HirExpression>,
}

impl<'output, 'hir> HirVisitor<'hir> for ConstructorCollector<'output, 'hir> {
    fn visit_expression(&mut self, expression: &'hir HirExpression) {
        if matches!(
            &expression.kind,
            HirExpressionKind::TupleConstructor { .. }
                | HirExpressionKind::ArrayConstructor { .. }
                | HirExpressionKind::ArrayRepeatConstructor { .. }
                | HirExpressionKind::StructConstructor { .. }
                | HirExpressionKind::EnumConstructor { .. }
        ) {
            self.output.push(expression);
        }
        walk_expression(self, expression);
    }
}

struct CallCollector<'output, 'hir> {
    output: &'output mut Vec<&'hir HirExpression>,
}

impl<'output, 'hir> HirVisitor<'hir> for CallCollector<'output, 'hir> {
    fn visit_expression(&mut self, expression: &'hir HirExpression) {
        if matches!(&expression.kind, HirExpressionKind::Call(_)) {
            self.output.push(expression);
        }
        walk_expression(self, expression);
    }
}

fn collect_constructors_in_block<'hir>(
    block: &'hir HirBlock,
    output: &mut Vec<&'hir HirExpression>,
) {
    ConstructorCollector { output }.visit_block(block);
}

fn collect_calls_in_block<'hir>(block: &'hir HirBlock, output: &mut Vec<&'hir HirExpression>) {
    CallCollector { output }.visit_block(block);
}

fn invalid_hir(source_span: ByteSpan) -> FrontendFailure {
    FrontendFailure::elaboration(source_span, "typed HIR violates VIR lowering invariants")
}
