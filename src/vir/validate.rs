use std::collections::{BTreeMap, BTreeSet};

use super::{
    SpannedVirInstruction, VirAbiErrorKind, VirBasicBlock, VirBlockId, VirBlockTarget,
    VirBorrowRegionConstraintId, VirBorrowRegionId, VirBorrowRegionOrigin, VirBorrowRegionScope,
    VirFieldId, VirFunction, VirFunctionId, VirIndexBounds, VirInstruction, VirInterfaceTransfer,
    VirLoanEffect, VirLoanId, VirLoanKind, VirLocation, VirMemoryAccess, VirMemorySchema,
    VirMemorySchemaErrorKind, VirMemoryTypeKind, VirMutability, VirObjectShapeErrorKind,
    VirOriginId, VirOriginKind, VirPointerKind, VirRuntimeSemanticProfile, VirSourceMapErrorKind,
    VirSpecBinderId, VirSpecClauseId, VirSpecClauseKind, VirSpecClauseOrigin, VirSpecTermId,
    VirTerminator, VirType, VirUnit, VirUnitVersion, VirValue, VirValueId,
};
use crate::ByteSpan;

/// A deterministic structural/type validation failure for a VIR unit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirValidationError {
    kind: VirValidationErrorKind,
    function: Option<VirFunctionId>,
    block: Option<VirBlockId>,
    source_span: Option<ByteSpan>,
}

impl VirValidationError {
    #[must_use]
    pub const fn kind(&self) -> &VirValidationErrorKind {
        &self.kind
    }

    #[must_use]
    pub const fn function(&self) -> Option<VirFunctionId> {
        self.function
    }

    #[must_use]
    pub const fn block(&self) -> Option<VirBlockId> {
        self.block
    }

    #[must_use]
    pub const fn source_span(&self) -> Option<ByteSpan> {
        self.source_span
    }
}

/// Machine-readable VIR validation error categories.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirValidationErrorKind {
    UnsupportedUnitVersion(VirUnitVersion),
    SemanticProfileMismatch {
        expected: VirRuntimeSemanticProfile,
        found: VirRuntimeSemanticProfile,
    },
    InvalidMemorySchema(VirMemorySchemaErrorKind),
    InvalidAggregateAbi(VirAbiErrorKind),
    InvalidSourceMap(VirSourceMapErrorKind),
    MissingFunctionContract(VirFunctionId),
    NonDenseContractId {
        expected: super::VirContractId,
        found: super::VirContractId,
    },
    ContractFunctionMismatch {
        contract: super::VirContractId,
        function: VirFunctionId,
    },
    DuplicateFunctionContract(VirFunctionId),
    ContractSignatureMismatch(super::VirContractId),
    NonDenseContractBinderId {
        contract: super::VirContractId,
        expected: super::VirContractBinderId,
        found: super::VirContractBinderId,
    },
    ContractBinderLayoutMismatch {
        contract: super::VirContractId,
        binder: super::VirContractBinderId,
    },
    NonDenseContractResourceId {
        contract: super::VirContractId,
        expected: super::VirContractResourceId,
        found: super::VirContractResourceId,
    },
    NonDenseSpecClauseId {
        expected: VirSpecClauseId,
        found: VirSpecClauseId,
    },
    NonDenseSpecBinderId {
        expected: VirSpecBinderId,
        found: VirSpecBinderId,
    },
    NonDenseSpecTermId {
        expected: VirSpecTermId,
        found: VirSpecTermId,
    },
    InvalidSpecBinder(VirSpecBinderId),
    InvalidSpecTerm(VirSpecTermId),
    SpecTermDepthExceeded(VirSpecTermId),
    InvalidSpecClauseOwner(VirSpecClauseId),
    InvalidSpecClauseLocation(VirSpecClauseId),
    InvalidSpecSnapshot(VirSpecTermId),
    InvalidPredicate(super::VirPredicateId),
    PredicateBodyFeatureGated(super::VirPredicateId),
    NonDensePredicateId {
        expected: super::VirPredicateId,
        found: super::VirPredicateId,
    },
    NonDenseSpecProveId {
        expected: super::VirSpecProveId,
        found: super::VirSpecProveId,
    },
    NonDenseTrustEntryId {
        expected: super::VirTrustEntryId,
        found: super::VirTrustEntryId,
    },
    NonDenseSpecLoopInvariantId {
        expected: super::VirSpecLoopInvariantId,
        found: super::VirSpecLoopInvariantId,
    },
    InvalidSpecProve(super::VirSpecProveId),
    InvalidTrustEntry(super::VirTrustEntryId),
    TrustPolicyDenied(super::VirTrustEntryId),
    LoopInvariantFeatureGated(super::VirSpecLoopInvariantId),
    UnknownSpecClauseOrigin(VirOriginId),
    SpecClauseOriginOutsideFunction(VirSpecClauseId),
    InvalidInferredTypeClause(VirSpecClauseId),
    MissingContractBinder(super::VirContractBinderId),
    ContractBinderPositionMismatch(super::VirContractBinderId),
    ContractBinderTypeMismatch(super::VirContractBinderId),
    DuplicateContractBinderFact(super::VirContractBinderId),
    MissingContractResource(super::VirContractResourceId),
    UnusedContractResource(super::VirContractResourceId),
    DuplicateContractResourceSummary(super::VirContractResourceId),
    InvalidContractRange(VirSpecClauseId),
    InvalidContractAlignment(VirSpecClauseId),
    InvalidContractAllocation(VirSpecClauseId),
    DeadOwnedContractResource(VirSpecClauseId),
    MissingCallContract(super::VirContractId),
    CallContractSignatureMismatch(super::VirContractId),
    EmptyProgram,
    MissingEntryFunction(VirFunctionId),
    DuplicateFunction(VirFunctionId),
    NonDenseBorrowRegionId {
        expected: VirBorrowRegionId,
        found: VirBorrowRegionId,
    },
    InvalidBorrowRegion(VirBorrowRegionId),
    NonDenseBorrowRegionConstraintId {
        expected: VirBorrowRegionConstraintId,
        found: VirBorrowRegionConstraintId,
    },
    InvalidBorrowRegionConstraint(VirBorrowRegionConstraintId),
    NonDenseLoanId {
        expected: VirLoanId,
        found: VirLoanId,
    },
    DuplicateLoanId(VirLoanId),
    MissingLoan(VirLoanId),
    InvalidLoanParent(VirLoanId),
    InvalidLoanEffect(VirLoanId),
    InvalidLoanReference(VirMemoryAccess),
    InvalidLoanRange(VirLoanId),
    LoanMetadataMismatch(VirLoanId),
    LoanEffectOutsideRegion(VirLoanId),
    LoanEffectOutOfOrder(VirLoanId),
    InvalidLoanEffectOrigin(VirLoanId),
    InvalidLoanAuthorityEffectOrigin,
    EmptyFunctionName,
    FunctionHasNoBlocks,
    MissingEntryBlock(VirBlockId),
    DuplicateBlock(VirBlockId),
    DuplicateValue(VirValueId),
    UndefinedValue(VirValueId),
    ValueNotAvailableInBlock(VirValueId),
    MissingTargetBlock(VirBlockId),
    TypeMismatch {
        context: &'static str,
        expected: VirType,
        found: VirType,
    },
    ArityMismatch {
        context: &'static str,
        expected: usize,
        found: usize,
    },
    InvalidAlignment(u64),
    InvalidMemoryAccess(VirMemoryAccess),
    InvalidLocalStorageShape(VirObjectShapeErrorKind),
    InvalidObjectEffectShape(VirObjectShapeErrorKind),
    ObjectEffectAliases,
    ResourcePermissionAliases,
    InvalidEnumObjectEffect(super::VirVariantId),
    ZeroSizedLocalStorage,
    LocalStorageOutsideEntry,
    LocalStorageAfterEntryInstruction,
    LocalStorageEntryReentered,
    InvalidFieldProjection(VirFieldId),
    InvalidTupleProjection(u64),
    InvalidObjectLeafProjection,
    InvalidIndexProjection,
    InvalidSliceRange,
    EmptyCallSymbol,
    SpanOutsideParent,
}

pub(super) fn validate(unit: &VirUnit) -> Result<(), VirValidationError> {
    if unit.version != VirUnitVersion::V18 {
        return Err(program_error(
            VirValidationErrorKind::UnsupportedUnitVersion(unit.version),
        ));
    }
    if let Some(expected) = VirRuntimeSemanticProfile::canonical_for(unit.version)
        && unit.runtime.semantic_profile != expected
    {
        return Err(program_error(
            VirValidationErrorKind::SemanticProfileMismatch {
                expected,
                found: unit.runtime.semantic_profile,
            },
        ));
    }
    unit.memory.validate().map_err(|error| {
        program_error(VirValidationErrorKind::InvalidMemorySchema(
            error.kind().clone(),
        ))
    })?;
    let runtime = &unit.runtime;
    if runtime.functions.is_empty() {
        return Err(program_error(VirValidationErrorKind::EmptyProgram));
    }

    let mut function_ids = BTreeSet::new();
    for function in &runtime.functions {
        if !function_ids.insert(function.id) {
            return Err(function_error(
                function,
                VirValidationErrorKind::DuplicateFunction(function.id),
                function.source_span,
            ));
        }
    }
    if !function_ids.contains(&runtime.entry) {
        return Err(program_error(VirValidationErrorKind::MissingEntryFunction(
            runtime.entry,
        )));
    }
    runtime
        .abis
        .validate(&unit.memory, &runtime.functions)
        .map_err(|error| {
            program_error(VirValidationErrorKind::InvalidAggregateAbi(
                error.kind().clone(),
            ))
        })?;
    validate_borrow_environment(unit)?;

    for function in &runtime.functions {
        validate_function(unit, function)?;
    }
    unit.source_map
        .validate(unit.version, runtime, additional_origins(unit))
        .map_err(|kind| program_error(VirValidationErrorKind::InvalidSourceMap(kind)))?;
    validate_loan_effect_origins(unit)?;
    validate_specs(unit)?;
    Ok(())
}

fn additional_origins(unit: &VirUnit) -> Vec<VirOriginId> {
    unit.borrows
        .regions()
        .iter()
        .map(|region| region.source_origin)
        .chain(
            unit.borrows
                .constraints()
                .iter()
                .map(|constraint| constraint.source_origin),
        )
        .chain(
            unit.specs
                .predicates()
                .iter()
                .map(|predicate| predicate.origin)
                .chain(unit.specs.binders().iter().map(|binder| binder.origin))
                .chain(unit.specs.terms().iter().map(|term| term.origin))
                .chain(
                    unit.specs
                        .clauses()
                        .iter()
                        .map(|clause| clause.origin.origin()),
                )
                .chain(unit.specs.proves().iter().map(|prove| prove.origin))
                .chain(unit.specs.trust_entries().iter().map(|entry| entry.origin))
                .chain(
                    unit.specs
                        .loop_invariants()
                        .iter()
                        .map(|invariant| invariant.origin),
                ),
        )
        .filter(|origin| unit.source_map.origin(*origin).is_some())
        .collect()
}

fn validate_borrow_environment(unit: &VirUnit) -> Result<(), VirValidationError> {
    let functions = unit
        .runtime
        .functions
        .iter()
        .map(|function| (function.id, function))
        .collect::<BTreeMap<_, _>>();

    for (index, region) in unit.borrows.regions().iter().enumerate() {
        let expected = VirBorrowRegionId::new(index as u32);
        if region.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseBorrowRegionId {
                    expected,
                    found: region.id,
                },
            ));
        }
        let valid = functions
            .get(&region.owner)
            .copied()
            .is_some_and(|function| {
                borrow_region_origin_is_anchored(unit, function, region.origin)
                    && borrow_region_scope_is_valid(function, region.origin, &region.scope)
                    && origin_is_within_function(unit, region.source_origin, function)
            });
        if !valid {
            return Err(program_error(VirValidationErrorKind::InvalidBorrowRegion(
                region.id,
            )));
        }
    }

    let mut relations = BTreeSet::new();
    for (index, constraint) in unit.borrows.constraints().iter().enumerate() {
        let expected = VirBorrowRegionConstraintId::new(index as u32);
        if constraint.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseBorrowRegionConstraintId {
                    expected,
                    found: constraint.id,
                },
            ));
        }
        let valid = constraint.subregion != constraint.superregion
            && functions
                .get(&constraint.owner)
                .copied()
                .is_some_and(|function| {
                    origin_is_within_function(unit, constraint.source_origin, function)
                })
            && unit
                .borrows
                .region(constraint.subregion)
                .is_some_and(|region| region.owner == constraint.owner)
            && unit
                .borrows
                .region(constraint.superregion)
                .is_some_and(|region| region.owner == constraint.owner)
            && relations.insert((
                constraint.owner,
                constraint.subregion,
                constraint.superregion,
            ));
        if !valid {
            return Err(program_error(
                VirValidationErrorKind::InvalidBorrowRegionConstraint(constraint.id),
            ));
        }
    }
    Ok(())
}

fn borrow_region_origin_is_anchored(
    unit: &VirUnit,
    function: &VirFunction,
    origin: VirBorrowRegionOrigin,
) -> bool {
    let Some(abi) = unit.runtime.abis.function(function.id) else {
        return false;
    };
    let binding = match origin {
        VirBorrowRegionOrigin::Parameter { index } => usize::try_from(index)
            .ok()
            .and_then(|index| abi.signature.parameters().get(index)),
        VirBorrowRegionOrigin::Result { index } => usize::try_from(index)
            .ok()
            .and_then(|index| abi.signature.results().get(index)),
        VirBorrowRegionOrigin::Lexical | VirBorrowRegionOrigin::Inferred => return true,
    };
    binding.is_some_and(|binding| {
        matches!(
            binding.interface().transfer,
            VirInterfaceTransfer::BorrowShared | VirInterfaceTransfer::BorrowMutable
        ) && binding.value().access().is_some_and(|access| {
            matches!(
                unit.memory.kind(access.ty),
                Some(
                    VirMemoryTypeKind::Pointer {
                        kind: VirPointerKind::Reference,
                        ..
                    } | VirMemoryTypeKind::Slice { .. }
                )
            )
        })
    })
}

fn borrow_region_scope_is_valid(
    function: &VirFunction,
    origin: VirBorrowRegionOrigin,
    scope: &VirBorrowRegionScope,
) -> bool {
    match (origin, scope) {
        (
            VirBorrowRegionOrigin::Parameter { .. } | VirBorrowRegionOrigin::Result { .. },
            VirBorrowRegionScope::Function,
        ) => true,
        (
            VirBorrowRegionOrigin::Lexical | VirBorrowRegionOrigin::Inferred,
            VirBorrowRegionScope::Blocks(blocks),
        ) => {
            !blocks.is_empty()
                && blocks.windows(2).all(|pair| pair[0] < pair[1])
                && blocks
                    .iter()
                    .all(|id| function.blocks.iter().any(|block| block.id == *id))
        }
        _ => false,
    }
}

fn origin_is_within_function(unit: &VirUnit, origin: VirOriginId, function: &VirFunction) -> bool {
    unit.source_map
        .source_span_for_origin(origin)
        .is_some_and(|source| span_contains(function.source_span, source.span))
}

fn validate_loan_effect_origins(unit: &VirUnit) -> Result<(), VirValidationError> {
    for function in &unit.runtime.functions {
        for block in &function.blocks {
            for (ordinal, spanned) in block.instructions.iter().enumerate() {
                let (origin_id, loan) = match &spanned.instruction {
                    VirInstruction::LoanBegin { effect, .. }
                    | VirInstruction::LoanAliasShared { effect, .. }
                    | VirInstruction::LoanReborrow { effect, .. }
                    | VirInstruction::LoanEnd { effect } => (effect.origin, Some(effect.loan)),
                    VirInstruction::LoanAliasAuthority { effect, .. }
                    | VirInstruction::LoanReborrowAuthority { effect, .. }
                    | VirInstruction::LoanEndAuthority { effect } => (effect.origin, None),
                    _ => continue,
                };
                let location = VirLocation::Instruction {
                    function: function.id,
                    block: block.id,
                    ordinal: ordinal as u64,
                };
                let valid = unit.source_map.origin_at(location).is_some_and(|origin| {
                    origin.id == origin_id
                        && matches!(
                            origin.kind,
                            VirOriginKind::Generated {
                                reason: super::VirGeneratedReason::LoanEffect,
                                ..
                            }
                        )
                });
                if !valid {
                    return Err(block_error(
                        function,
                        block,
                        loan.map_or(
                            VirValidationErrorKind::InvalidLoanAuthorityEffectOrigin,
                            VirValidationErrorKind::InvalidLoanEffectOrigin,
                        ),
                        spanned.source_span,
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_specs(unit: &VirUnit) -> Result<(), VirValidationError> {
    let functions = unit
        .runtime
        .functions
        .iter()
        .map(|function| (function.id, function))
        .collect::<BTreeMap<_, _>>();
    let mut owners = BTreeSet::new();

    for (index, clause) in unit.specs.clauses().iter().enumerate() {
        let expected = VirSpecClauseId::new(index as u32);
        if clause.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseSpecClauseId {
                    expected,
                    found: clause.id,
                },
            ));
        }
    }

    for (index, contract) in unit.specs.contracts().iter().enumerate() {
        let expected = super::VirContractId::new(index as u32);
        if contract.id != expected {
            return Err(program_error(VirValidationErrorKind::NonDenseContractId {
                expected,
                found: contract.id,
            }));
        }
        let Some(function) = functions.get(&contract.function).copied() else {
            return Err(program_error(
                VirValidationErrorKind::ContractFunctionMismatch {
                    contract: contract.id,
                    function: contract.function,
                },
            ));
        };
        if !owners.insert(contract.function) {
            return Err(function_error(
                function,
                VirValidationErrorKind::DuplicateFunctionContract(contract.function),
                function.source_span,
            ));
        }
        if function.contract != contract.id {
            return Err(function_error(
                function,
                VirValidationErrorKind::ContractFunctionMismatch {
                    contract: contract.id,
                    function: contract.function,
                },
                function.source_span,
            ));
        }
        if function.signature != contract.signature {
            return Err(function_error(
                function,
                VirValidationErrorKind::ContractSignatureMismatch(contract.id),
                function.source_span,
            ));
        }
        validate_contract(unit, function, contract)?;
    }

    for function in &unit.runtime.functions {
        if !owners.contains(&function.id) {
            return Err(function_error(
                function,
                VirValidationErrorKind::MissingFunctionContract(function.id),
                function.source_span,
            ));
        }
        for block in &function.blocks {
            for instruction in &block.instructions {
                let VirInstruction::Call { target, .. } = &instruction.instruction else {
                    continue;
                };
                let Some(contract) = unit.specs.contract(target.contract) else {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::MissingCallContract(target.contract),
                        instruction.source_span,
                    ));
                };
                if contract.signature != target.signature {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::CallContractSignatureMismatch(target.contract),
                        instruction.source_span,
                    ));
                }
            }
        }
    }
    validate_pure_specs(unit, &functions)
}

fn validate_contract(
    unit: &VirUnit,
    function: &VirFunction,
    contract: &super::VirContract,
) -> Result<(), VirValidationError> {
    let function_source_span = unit
        .source_map
        .source_span(VirLocation::FunctionEntry {
            function: function.id,
        })
        .expect("validated source map covers every function entry");
    let expected_binders = contract
        .signature
        .parameters
        .iter()
        .copied()
        .enumerate()
        .map(|(slot, ty)| (super::VirContractPosition::Requires, slot as u32, ty))
        .chain(
            contract
                .signature
                .results
                .iter()
                .copied()
                .enumerate()
                .map(|(slot, ty)| (super::VirContractPosition::Ensures, slot as u32, ty)),
        )
        .collect::<Vec<_>>();
    if contract.binders.len() != expected_binders.len() {
        let binder = contract
            .binders
            .get(
                expected_binders
                    .len()
                    .min(contract.binders.len())
                    .saturating_sub(1),
            )
            .map_or(super::VirContractBinderId::new(0), |binder| binder.id);
        return Err(function_error(
            function,
            VirValidationErrorKind::ContractBinderLayoutMismatch {
                contract: contract.id,
                binder,
            },
            function.source_span,
        ));
    }
    for (index, (binder, expected_layout)) in
        contract.binders.iter().zip(expected_binders).enumerate()
    {
        let expected_id = super::VirContractBinderId::new(index as u32);
        if binder.id != expected_id {
            return Err(function_error(
                function,
                VirValidationErrorKind::NonDenseContractBinderId {
                    contract: contract.id,
                    expected: expected_id,
                    found: binder.id,
                },
                function.source_span,
            ));
        }
        if (binder.position, binder.slot, binder.ty) != expected_layout {
            return Err(function_error(
                function,
                VirValidationErrorKind::ContractBinderLayoutMismatch {
                    contract: contract.id,
                    binder: binder.id,
                },
                function.source_span,
            ));
        }
    }
    for (index, resource) in contract.resources.iter().enumerate() {
        let expected = super::VirContractResourceId::new(index as u32);
        if resource.id != expected {
            return Err(function_error(
                function,
                VirValidationErrorKind::NonDenseContractResourceId {
                    contract: contract.id,
                    expected,
                    found: resource.id,
                },
                function.source_span,
            ));
        }
    }

    let mut used_resources = BTreeSet::new();
    let mut summarized_resources = BTreeSet::new();
    let mut defined_binders = BTreeSet::new();
    let mut previous_clause = None;
    for clause_id in &contract.clauses {
        if previous_clause.is_some_and(|previous| previous >= *clause_id) {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidSpecClauseOwner(*clause_id),
                function.source_span,
            ));
        }
        previous_clause = Some(*clause_id);
        let Some(clause) = unit.specs.clause(*clause_id) else {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidSpecClauseOwner(*clause_id),
                function.source_span,
            ));
        };
        let Some(position) = contract_clause_position(contract.id, clause) else {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
                function.source_span,
            ));
        };
        let expected_location = match position {
            super::VirContractPosition::Requires => super::VirSpecLocation::FunctionEntry {
                function: function.id,
            },
            super::VirContractPosition::Ensures => super::VirSpecLocation::FunctionResult {
                function: function.id,
            },
        };
        if clause.location != expected_location {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidSpecClauseLocation(clause.id),
                function.source_span,
            ));
        }
        let origin_id = clause.origin.origin();
        let Some(source_span) = unit.source_map.source_span_for_origin(origin_id) else {
            return Err(function_error(
                function,
                VirValidationErrorKind::UnknownSpecClauseOrigin(origin_id),
                function.source_span,
            ));
        };
        if source_span.source != function_source_span.source
            || !span_contains(function_source_span.span, source_span.span)
        {
            return Err(function_error(
                function,
                VirValidationErrorKind::SpecClauseOriginOutsideFunction(clause.id),
                source_span.span,
            ));
        }
        if matches!(clause.origin, VirSpecClauseOrigin::InferredType { .. })
            && !matches!(clause.kind, VirSpecClauseKind::Resource(_))
        {
            return Err(function_error(
                function,
                VirValidationErrorKind::InvalidInferredTypeClause(clause.id),
                source_span.span,
            ));
        }
        match &clause.kind {
            VirSpecClauseKind::Resource(summary) => {
                if contract
                    .resources
                    .get(summary.resource.get() as usize)
                    .is_none_or(|resource| resource.id != summary.resource)
                {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::MissingContractResource(summary.resource),
                        source_span.span,
                    ));
                }
                used_resources.insert(summary.resource);
                if !summarized_resources.insert((position, summary.resource)) {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::DuplicateContractResourceSummary(summary.resource),
                        source_span.span,
                    ));
                }
                if summary.size_bytes == 0
                    || summary.alignment == 0
                    || !summary.alignment.is_power_of_two()
                {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::InvalidContractAllocation(clause.id),
                        source_span.span,
                    ));
                }
                if matches!(summary.liveness, super::VirContractLiveness::Dead)
                    && matches!(summary.ownership, super::VirContractOwnership::Owned)
                {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::DeadOwnedContractResource(clause.id),
                        source_span.span,
                    ));
                }
                for pointer in &summary.pointers {
                    validate_pointer_clause_binder(
                        function,
                        contract,
                        clause,
                        pointer.binder,
                        &mut defined_binders,
                        source_span.span,
                    )?;
                    if pointer.offset_lower > pointer.offset_upper {
                        return Err(function_error(
                            function,
                            VirValidationErrorKind::InvalidContractRange(clause.id),
                            source_span.span,
                        ));
                    }
                    if pointer.alignment == 0 || !pointer.alignment.is_power_of_two() {
                        return Err(function_error(
                            function,
                            VirValidationErrorKind::InvalidContractAlignment(clause.id),
                            source_span.span,
                        ));
                    }
                }
                for permission in &summary.permissions {
                    validate_clause_binder(
                        function,
                        contract,
                        clause,
                        permission.binder,
                        VirType::Permission,
                        &mut defined_binders,
                        source_span.span,
                    )?;
                    if permission.start_byte >= permission.end_byte
                        || permission.end_byte > summary.size_bytes
                    {
                        return Err(function_error(
                            function,
                            VirValidationErrorKind::InvalidContractRange(clause.id),
                            source_span.span,
                        ));
                    }
                }
            }
            VirSpecClauseKind::U64Range {
                binder,
                lower,
                upper,
            } => {
                validate_clause_binder(
                    function,
                    contract,
                    clause,
                    *binder,
                    VirType::U64,
                    &mut defined_binders,
                    source_span.span,
                )?;
                if lower > upper {
                    return Err(function_error(
                        function,
                        VirValidationErrorKind::InvalidContractRange(clause.id),
                        source_span.span,
                    ));
                }
            }
            VirSpecClauseKind::BoolValue { binder, .. } => validate_clause_binder(
                function,
                contract,
                clause,
                *binder,
                VirType::Bool,
                &mut defined_binders,
                source_span.span,
            )?,
            VirSpecClauseKind::Logic { .. } => {}
        }
    }
    for resource in &contract.resources {
        if !used_resources.contains(&resource.id) {
            return Err(function_error(
                function,
                VirValidationErrorKind::UnusedContractResource(resource.id),
                function.source_span,
            ));
        }
    }
    Ok(())
}

fn validate_pure_specs(
    unit: &VirUnit,
    functions: &BTreeMap<VirFunctionId, &VirFunction>,
) -> Result<(), VirValidationError> {
    const MAX_SPEC_TERM_DEPTH: usize = 256;

    let mut predicate_names = BTreeSet::new();
    for (index, predicate) in unit.specs.predicates().iter().enumerate() {
        let expected = super::VirPredicateId::new(index as u32);
        if predicate.id != expected {
            return Err(program_error(VirValidationErrorKind::NonDensePredicateId {
                expected,
                found: predicate.id,
            }));
        }
        let mut predicate_binders = BTreeSet::new();
        if predicate.name.is_empty()
            || !predicate_names.insert(predicate.name.as_str())
            || unit
                .source_map
                .source_span_for_origin(predicate.origin)
                .is_none()
            || !predicate.binders.iter().all(|binder_id| {
                predicate_binders.insert(*binder_id)
                    && unit
                        .specs
                        .binders()
                        .get(binder_id.get() as usize)
                        .is_some_and(|binder| {
                            binder.id == *binder_id
                                && binder.owner
                                    == super::VirSpecBinderOwner::Predicate(predicate.id)
                        })
            })
        {
            return Err(program_error(VirValidationErrorKind::InvalidPredicate(
                predicate.id,
            )));
        }
        if predicate.body.is_some() {
            return Err(program_error(
                VirValidationErrorKind::PredicateBodyFeatureGated(predicate.id),
            ));
        }
    }

    let mut binder_names = BTreeSet::new();
    for (index, binder) in unit.specs.binders().iter().enumerate() {
        let expected = VirSpecBinderId::new(index as u32);
        if binder.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseSpecBinderId {
                    expected,
                    found: binder.id,
                },
            ));
        }
        let owner_valid = match binder.owner {
            super::VirSpecBinderOwner::Clause(clause_id) => unit
                .specs
                .clause(clause_id)
                .and_then(|clause| {
                    clause_owner_function(unit, clause)
                        .map(|function| origin_belongs_to_function(unit, function, binder.origin))
                })
                .unwrap_or(false),
            super::VirSpecBinderOwner::Predicate(predicate_id) => unit
                .specs
                .predicates()
                .get(predicate_id.get() as usize)
                .is_some_and(|predicate| {
                    predicate.id == predicate_id
                        && predicate.binders.contains(&binder.id)
                        && origins_are_nested(unit, predicate.origin, binder.origin)
                }),
        };
        if binder.name.is_empty()
            || !binder_names.insert((binder.owner, binder.name.as_str()))
            || !owner_valid
            || unit
                .source_map
                .source_span_for_origin(binder.origin)
                .is_none()
        {
            return Err(program_error(VirValidationErrorKind::InvalidSpecBinder(
                binder.id,
            )));
        }
    }

    let mut depths = Vec::with_capacity(unit.specs.terms().len());
    for (index, term) in unit.specs.terms().iter().enumerate() {
        let expected = VirSpecTermId::new(index as u32);
        if term.id != expected {
            return Err(program_error(VirValidationErrorKind::NonDenseSpecTermId {
                expected,
                found: term.id,
            }));
        }
        let Some(clause) = unit.specs.clause(term.clause) else {
            return Err(program_error(VirValidationErrorKind::InvalidSpecTerm(
                term.id,
            )));
        };
        let Some(function) = clause_owner_function(unit, clause) else {
            return Err(program_error(
                VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
            ));
        };
        if !origin_belongs_to_function(unit, function, term.origin) {
            return Err(program_error(VirValidationErrorKind::InvalidSpecTerm(
                term.id,
            )));
        }
        let child = |id: VirSpecTermId| {
            unit.specs
                .terms()
                .get(id.get() as usize)
                .filter(|child| child.id == id && id.get() < term.id.get())
                .filter(|child| child.clause == term.clause)
        };
        let (valid, depth) = match &term.kind {
            super::VirSpecTermKind::Bool(_) => (term.ty == super::VirSpecType::Bool, 1),
            super::VirSpecTermKind::U64(_) => (term.ty == super::VirSpecType::U64, 1),
            super::VirSpecTermKind::Binder(id) => {
                let valid = unit
                    .specs
                    .binders()
                    .get(id.get() as usize)
                    .is_some_and(|binder| {
                        binder.id == *id
                            && binder.owner == super::VirSpecBinderOwner::Clause(term.clause)
                            && binder.ty == term.ty
                    });
                (valid, 1)
            }
            super::VirSpecTermKind::Snapshot(snapshot) => {
                (validate_spec_snapshot(unit, clause, term.ty, *snapshot), 1)
            }
            super::VirSpecTermKind::Equal { left, right } => {
                let valid = term.ty == super::VirSpecType::Bool
                    && child(*left)
                        .zip(child(*right))
                        .is_some_and(|(left, right)| left.ty == right.ty);
                (valid, spec_binary_depth(&depths, *left, *right))
            }
            super::VirSpecTermKind::LessThan { left, right }
            | super::VirSpecTermKind::LessOrEqual { left, right } => {
                let valid = term.ty == super::VirSpecType::Bool
                    && child(*left).is_some_and(|left| left.ty == super::VirSpecType::U64)
                    && child(*right).is_some_and(|right| right.ty == super::VirSpecType::U64);
                (valid, spec_binary_depth(&depths, *left, *right))
            }
            super::VirSpecTermKind::Not(operand) => {
                let valid = term.ty == super::VirSpecType::Bool
                    && child(*operand)
                        .is_some_and(|operand| operand.ty == super::VirSpecType::Bool);
                (valid, spec_unary_depth(&depths, *operand))
            }
            super::VirSpecTermKind::And(operands) | super::VirSpecTermKind::Or(operands) => {
                let valid = term.ty == super::VirSpecType::Bool
                    && operands.len() >= 2
                    && operands.iter().all(|operand| {
                        child(*operand)
                            .is_some_and(|operand| operand.ty == super::VirSpecType::Bool)
                    });
                (valid, spec_nary_depth(&depths, operands))
            }
        };
        if !valid {
            let kind = if matches!(term.kind, super::VirSpecTermKind::Snapshot(_)) {
                VirValidationErrorKind::InvalidSpecSnapshot(term.id)
            } else {
                VirValidationErrorKind::InvalidSpecTerm(term.id)
            };
            return Err(program_error(kind));
        }
        if depth > MAX_SPEC_TERM_DEPTH {
            return Err(program_error(
                VirValidationErrorKind::SpecTermDepthExceeded(term.id),
            ));
        }
        depths.push(depth);
    }

    for clause in unit.specs.clauses() {
        let Some(function) = clause_owner_function(unit, clause) else {
            return Err(program_error(
                VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
            ));
        };
        if !clause_owner_has_backlink(unit, clause) {
            return Err(program_error(
                VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
            ));
        }
        if !spec_location_exists(unit, clause.location)
            || clause.location.function() != function
            || !origin_belongs_to_function(unit, function, clause.origin.origin())
        {
            return Err(program_error(
                VirValidationErrorKind::InvalidSpecClauseLocation(clause.id),
            ));
        }
        if matches!(clause.origin, VirSpecClauseOrigin::InferredType { .. })
            && !matches!(clause.kind, VirSpecClauseKind::Resource(_))
        {
            return Err(program_error(
                VirValidationErrorKind::InvalidInferredTypeClause(clause.id),
            ));
        }
        match clause.kind {
            VirSpecClauseKind::Logic { root } => {
                if !unit
                    .specs
                    .terms()
                    .get(root.get() as usize)
                    .is_some_and(|term| {
                        term.id == root
                            && term.clause == clause.id
                            && term.ty == super::VirSpecType::Bool
                    })
                {
                    return Err(program_error(VirValidationErrorKind::InvalidSpecTerm(root)));
                }
            }
            _ if !matches!(clause.owner, super::VirSpecClauseOwner::Contract { .. }) => {
                return Err(program_error(
                    VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
                ));
            }
            _ => {}
        }
    }

    for (index, prove) in unit.specs.proves().iter().enumerate() {
        let expected = super::VirSpecProveId::new(index as u32);
        if prove.id != expected {
            return Err(program_error(VirValidationErrorKind::NonDenseSpecProveId {
                expected,
                found: prove.id,
            }));
        }
        let valid = functions.contains_key(&prove.function)
            && spec_location_exists(unit, prove.location)
            && prove.location.function() == prove.function
            && unit.specs.clause(prove.clause).is_some_and(|clause| {
                clause.owner == super::VirSpecClauseOwner::Prove(prove.id)
                    && clause.location == prove.location
                    && matches!(clause.kind, VirSpecClauseKind::Logic { .. })
            })
            && origin_belongs_to_function(unit, prove.function, prove.origin);
        if !valid {
            return Err(program_error(VirValidationErrorKind::InvalidSpecProve(
                prove.id,
            )));
        }
    }

    for (index, entry) in unit.specs.trust_entries().iter().enumerate() {
        let expected = super::VirTrustEntryId::new(index as u32);
        if entry.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseTrustEntryId {
                    expected,
                    found: entry.id,
                },
            ));
        }
        if entry.policy != super::VirTrustPolicyKind::EntryPointAssumption
            || entry.scope
                != (super::VirTrustScope::FunctionEntry {
                    function: unit.runtime.entry,
                })
        {
            return Err(program_error(VirValidationErrorKind::TrustPolicyDenied(
                entry.id,
            )));
        }
        let valid = functions.contains_key(&entry.scope.function())
            && unit.specs.clause(entry.clause).is_some_and(|clause| {
                clause.owner == super::VirSpecClauseOwner::TrustEntry(entry.id)
                    && clause.location == entry.scope.location()
                    && clause.origin
                        == super::VirSpecClauseOrigin::Explicit {
                            origin: entry.origin,
                        }
                    && matches!(clause.kind, VirSpecClauseKind::Logic { .. })
            })
            && origin_belongs_to_function(unit, entry.scope.function(), entry.origin);
        if !valid {
            return Err(program_error(VirValidationErrorKind::InvalidTrustEntry(
                entry.id,
            )));
        }
    }

    for (index, invariant) in unit.specs.loop_invariants().iter().enumerate() {
        let expected = super::VirSpecLoopInvariantId::new(index as u32);
        if invariant.id != expected {
            return Err(program_error(
                VirValidationErrorKind::NonDenseSpecLoopInvariantId {
                    expected,
                    found: invariant.id,
                },
            ));
        }
    }
    if let Some(invariant) = unit.specs.loop_invariants().first() {
        return Err(program_error(
            VirValidationErrorKind::LoopInvariantFeatureGated(invariant.id),
        ));
    }
    Ok(())
}

fn clause_owner_function(unit: &VirUnit, clause: &super::VirSpecClause) -> Option<VirFunctionId> {
    match clause.owner {
        super::VirSpecClauseOwner::Contract { contract, .. } => unit
            .specs
            .contract(contract)
            .map(|contract| contract.function),
        super::VirSpecClauseOwner::Prove(prove_id) => unit
            .specs
            .proves()
            .get(prove_id.get() as usize)
            .filter(|prove| prove.id == prove_id)
            .map(|prove| prove.function),
        super::VirSpecClauseOwner::TrustEntry(entry_id) => unit
            .specs
            .trust_entries()
            .get(entry_id.get() as usize)
            .filter(|entry| entry.id == entry_id)
            .map(|entry| entry.scope.function()),
        super::VirSpecClauseOwner::LoopInvariant(invariant_id) => unit
            .specs
            .loop_invariants()
            .get(invariant_id.get() as usize)
            .filter(|invariant| invariant.id == invariant_id)
            .map(|invariant| invariant.function),
    }
}

fn clause_owner_has_backlink(unit: &VirUnit, clause: &super::VirSpecClause) -> bool {
    match clause.owner {
        super::VirSpecClauseOwner::Contract { contract, .. } => unit
            .specs
            .contract(contract)
            .is_some_and(|contract| contract.clauses.contains(&clause.id)),
        super::VirSpecClauseOwner::Prove(prove_id) => unit
            .specs
            .proves()
            .get(prove_id.get() as usize)
            .is_some_and(|prove| prove.id == prove_id && prove.clause == clause.id),
        super::VirSpecClauseOwner::TrustEntry(entry_id) => unit
            .specs
            .trust_entries()
            .get(entry_id.get() as usize)
            .is_some_and(|entry| entry.id == entry_id && entry.clause == clause.id),
        super::VirSpecClauseOwner::LoopInvariant(invariant_id) => unit
            .specs
            .loop_invariants()
            .get(invariant_id.get() as usize)
            .is_some_and(|invariant| invariant.id == invariant_id && invariant.clause == clause.id),
    }
}

fn origins_are_nested(unit: &VirUnit, parent: VirOriginId, child: VirOriginId) -> bool {
    unit.source_map
        .source_span_for_origin(parent)
        .zip(unit.source_map.source_span_for_origin(child))
        .is_some_and(|(parent, child)| {
            parent.source == child.source && span_contains(parent.span, child.span)
        })
}

fn spec_location_exists(unit: &VirUnit, location: super::VirSpecLocation) -> bool {
    match location {
        super::VirSpecLocation::FunctionEntry { function }
        | super::VirSpecLocation::FunctionResult { function } => unit
            .runtime
            .functions
            .iter()
            .any(|candidate| candidate.id == function),
        super::VirSpecLocation::Runtime(location) => unit.source_map.origin_at(location).is_some(),
    }
}

fn origin_belongs_to_function(
    unit: &VirUnit,
    function: VirFunctionId,
    origin: VirOriginId,
) -> bool {
    unit.source_map
        .source_span(VirLocation::FunctionEntry { function })
        .zip(unit.source_map.source_span_for_origin(origin))
        .is_some_and(|(function_span, origin_span)| {
            function_span.source == origin_span.source
                && span_contains(function_span.span, origin_span.span)
        })
}

fn validate_spec_snapshot(
    unit: &VirUnit,
    clause: &super::VirSpecClause,
    ty: super::VirSpecType,
    snapshot: super::VirSpecSnapshot,
) -> bool {
    match snapshot {
        super::VirSpecSnapshot::Parameter { function, slot } => unit
            .runtime
            .functions
            .iter()
            .find(|candidate| candidate.id == function)
            .and_then(|function| function.signature.parameters.get(slot as usize))
            .is_some_and(|runtime_ty| {
                clause.location == super::VirSpecLocation::FunctionEntry { function }
                    && spec_type_matches_runtime(ty, *runtime_ty)
            }),
        super::VirSpecSnapshot::Result { function, slot } => unit
            .runtime
            .functions
            .iter()
            .find(|candidate| candidate.id == function)
            .and_then(|function| function.signature.results.get(slot as usize))
            .is_some_and(|runtime_ty| {
                clause.location == super::VirSpecLocation::FunctionResult { function }
                    && spec_type_matches_runtime(ty, *runtime_ty)
            }),
        super::VirSpecSnapshot::Value { function, value } => {
            validate_runtime_snapshot(unit, clause, ty, function, value)
        }
    }
}

fn validate_runtime_snapshot(
    unit: &VirUnit,
    clause: &super::VirSpecClause,
    ty: super::VirSpecType,
    function_id: VirFunctionId,
    value: VirValueId,
) -> bool {
    let super::VirSpecLocation::Runtime(location) = clause.location else {
        return false;
    };
    if location.function() != function_id {
        return false;
    }
    let Some(block_id) = location.block() else {
        return false;
    };
    let Some(function) = unit
        .runtime
        .functions
        .iter()
        .find(|function| function.id == function_id)
    else {
        return false;
    };
    let Some(block) = function.blocks.iter().find(|block| block.id == block_id) else {
        return false;
    };
    if let Some(parameter) = block
        .parameters
        .iter()
        .find(|parameter| parameter.id == value)
    {
        return spec_type_matches_runtime(ty, parameter.ty);
    }
    for (definition, instruction) in block.instructions.iter().enumerate() {
        let mut found = None;
        instruction.instruction.visit_results(|result| {
            if result.id == value {
                found = Some(result.ty);
            }
        });
        let Some(runtime_ty) = found else { continue };
        let available = match location {
            VirLocation::Instruction { ordinal, .. } => definition as u64 <= ordinal,
            VirLocation::CallEdge { instruction, .. } => definition as u64 <= instruction,
            VirLocation::Terminator { .. } => true,
            VirLocation::FunctionEntry { .. }
            | VirLocation::BlockEntry { .. }
            | VirLocation::BlockParameter { .. } => false,
        };
        return available && spec_type_matches_runtime(ty, runtime_ty);
    }
    false
}

const fn spec_type_matches_runtime(spec: super::VirSpecType, runtime: VirType) -> bool {
    matches!(
        (spec, runtime),
        (super::VirSpecType::Bool, VirType::Bool) | (super::VirSpecType::U64, VirType::U64)
    )
}

fn spec_unary_depth(depths: &[usize], operand: VirSpecTermId) -> usize {
    depths
        .get(operand.get() as usize)
        .and_then(|depth| depth.checked_add(1))
        .unwrap_or(usize::MAX)
}

fn spec_binary_depth(depths: &[usize], left: VirSpecTermId, right: VirSpecTermId) -> usize {
    depths
        .get(left.get() as usize)
        .zip(depths.get(right.get() as usize))
        .and_then(|(left, right)| left.max(right).checked_add(1))
        .unwrap_or(usize::MAX)
}

fn spec_nary_depth(depths: &[usize], operands: &[VirSpecTermId]) -> usize {
    operands
        .iter()
        .map(|operand| depths.get(operand.get() as usize).copied())
        .collect::<Option<Vec<_>>>()
        .and_then(|depths| depths.into_iter().max())
        .and_then(|depth| depth.checked_add(1))
        .unwrap_or(usize::MAX)
}

fn validate_clause_binder(
    function: &VirFunction,
    contract: &super::VirContract,
    clause: &super::VirSpecClause,
    binder_id: super::VirContractBinderId,
    expected_type: VirType,
    defined_binders: &mut BTreeSet<super::VirContractBinderId>,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let Some(position) = contract_clause_position(contract.id, clause) else {
        return Err(function_error(
            function,
            VirValidationErrorKind::InvalidSpecClauseOwner(clause.id),
            source_span,
        ));
    };
    let Some(binder) = contract.binders.get(binder_id.get() as usize) else {
        return Err(function_error(
            function,
            VirValidationErrorKind::MissingContractBinder(binder_id),
            source_span,
        ));
    };
    if binder.id != binder_id {
        return Err(function_error(
            function,
            VirValidationErrorKind::MissingContractBinder(binder_id),
            source_span,
        ));
    }
    if binder.position != position {
        return Err(function_error(
            function,
            VirValidationErrorKind::ContractBinderPositionMismatch(binder_id),
            source_span,
        ));
    }
    if binder.ty != expected_type {
        return Err(function_error(
            function,
            VirValidationErrorKind::ContractBinderTypeMismatch(binder_id),
            source_span,
        ));
    }
    if !defined_binders.insert(binder_id) {
        return Err(function_error(
            function,
            VirValidationErrorKind::DuplicateContractBinderFact(binder_id),
            source_span,
        ));
    }
    Ok(())
}

fn validate_pointer_clause_binder(
    function: &VirFunction,
    contract: &super::VirContract,
    clause: &super::VirSpecClause,
    binder_id: super::VirContractBinderId,
    defined_binders: &mut BTreeSet<super::VirContractBinderId>,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let Some(binder) = contract.binders.get(binder_id.get() as usize) else {
        return Err(function_error(
            function,
            VirValidationErrorKind::MissingContractBinder(binder_id),
            source_span,
        ));
    };
    if !matches!(binder.ty, VirType::Pointer { .. }) {
        return Err(function_error(
            function,
            VirValidationErrorKind::ContractBinderTypeMismatch(binder_id),
            source_span,
        ));
    }
    validate_clause_binder(
        function,
        contract,
        clause,
        binder_id,
        binder.ty,
        defined_binders,
        source_span,
    )
}

fn contract_clause_position(
    contract: super::VirContractId,
    clause: &super::VirSpecClause,
) -> Option<super::VirContractPosition> {
    match clause.owner {
        super::VirSpecClauseOwner::Contract {
            contract: owner,
            position,
        } if owner == contract => Some(position),
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct LoanDefinition {
    effect: VirLoanEffect,
    order: usize,
}

struct LoanValidationContext<'unit> {
    unit: &'unit VirUnit,
    definitions: BTreeMap<VirLoanId, LoanDefinition>,
    orders: BTreeMap<(VirBlockId, usize), usize>,
}

impl LoanValidationContext<'_> {
    fn order(&self, block: VirBlockId, instruction: usize) -> usize {
        self.orders[&(block, instruction)]
    }
}

fn validate_function(unit: &VirUnit, function: &VirFunction) -> Result<(), VirValidationError> {
    let memory = &unit.memory;
    if function.name.is_empty() {
        return Err(function_error(
            function,
            VirValidationErrorKind::EmptyFunctionName,
            function.source_span,
        ));
    }
    if function.blocks.is_empty() {
        return Err(function_error(
            function,
            VirValidationErrorKind::FunctionHasNoBlocks,
            function.source_span,
        ));
    }
    for ty in function
        .signature
        .parameters
        .iter()
        .chain(&function.signature.results)
    {
        validate_declared_type(memory, function, None, *ty, function.source_span)?;
    }

    let mut blocks = BTreeMap::new();
    for block in &function.blocks {
        if !span_contains(function.source_span, block.source_span) {
            return Err(block_error(
                function,
                block,
                VirValidationErrorKind::SpanOutsideParent,
                block.source_span,
            ));
        }
        if blocks.insert(block.id, block).is_some() {
            return Err(block_error(
                function,
                block,
                VirValidationErrorKind::DuplicateBlock(block.id),
                block.source_span,
            ));
        }
    }
    let Some(entry) = blocks.get(&function.entry).copied() else {
        return Err(function_error(
            function,
            VirValidationErrorKind::MissingEntryBlock(function.entry),
            function.source_span,
        ));
    };
    check_types(
        function,
        entry,
        "function entry parameters",
        &function.signature.parameters,
        &entry.parameters,
    )?;

    validate_local_storage_placement(function)?;

    let loans = collect_loan_definitions(unit, function)?;
    let definitions = collect_definitions(memory, function)?;
    for block in &function.blocks {
        validate_block(function, block, &blocks, &definitions, &loans)?;
    }
    Ok(())
}

fn collect_loan_definitions<'unit>(
    unit: &'unit VirUnit,
    function: &VirFunction,
) -> Result<LoanValidationContext<'unit>, VirValidationError> {
    let mut definitions = BTreeMap::new();
    let mut authority_definitions = BTreeSet::new();
    let mut orders = BTreeMap::new();
    let mut order = 0_usize;
    let mut next_loan = 0_u32;
    for block in &function.blocks {
        for (instruction_index, spanned) in block.instructions.iter().enumerate() {
            orders.insert((block.id, instruction_index), order);
            if let VirInstruction::LoanReborrowAuthority { loan, .. } = spanned.instruction {
                if definitions.contains_key(&loan) || !authority_definitions.insert(loan) {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::DuplicateLoanId(loan),
                        spanned.source_span,
                    ));
                }
                if loan.get() != next_loan || loan.get() >= (1 << 31) {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::NonDenseLoanId {
                            expected: VirLoanId::new(next_loan),
                            found: loan,
                        },
                        spanned.source_span,
                    ));
                }
                next_loan = next_loan.checked_add(1).ok_or_else(|| {
                    block_error(
                        function,
                        block,
                        VirValidationErrorKind::InvalidLoanEffect(loan),
                        spanned.source_span,
                    )
                })?;
            }
            let (effect, is_reborrow) = match &spanned.instruction {
                VirInstruction::LoanBegin { effect, .. } => (Some(*effect), false),
                VirInstruction::LoanReborrow { effect, .. } => (Some(*effect), true),
                _ => (None, false),
            };
            if let Some(effect) = effect {
                if definitions.contains_key(&effect.loan)
                    || authority_definitions.contains(&effect.loan)
                {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::DuplicateLoanId(effect.loan),
                        spanned.source_span,
                    ));
                }
                let expected = VirLoanId::new(next_loan);
                if effect.loan != expected || effect.loan.get() >= (1 << 31) {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::NonDenseLoanId {
                            expected,
                            found: effect.loan,
                        },
                        spanned.source_span,
                    ));
                }
                let parent_shape_valid = if is_reborrow {
                    effect
                        .parent
                        .is_some_and(|parent| parent.get() < effect.loan.get())
                } else {
                    effect.parent.is_none()
                };
                if !parent_shape_valid {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::InvalidLoanParent(effect.loan),
                        spanned.source_span,
                    ));
                }
                definitions.insert(effect.loan, LoanDefinition { effect, order });
                next_loan = next_loan.checked_add(1).ok_or_else(|| {
                    block_error(
                        function,
                        block,
                        VirValidationErrorKind::InvalidLoanEffect(effect.loan),
                        spanned.source_span,
                    )
                })?;
            }
            order = order.checked_add(1).ok_or_else(|| {
                block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidLoanEffect(VirLoanId::new(next_loan)),
                    spanned.source_span,
                )
            })?;
        }
    }
    Ok(LoanValidationContext {
        unit,
        definitions,
        orders,
    })
}

fn validate_local_storage_placement(function: &VirFunction) -> Result<(), VirValidationError> {
    let mut has_local_storage = false;
    let mut entry_prefix_ended = false;
    for block in &function.blocks {
        for spanned in &block.instructions {
            if matches!(spanned.instruction, VirInstruction::LocalStorage { .. }) {
                has_local_storage = true;
                if block.id != function.entry {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::LocalStorageOutsideEntry,
                        spanned.source_span,
                    ));
                }
                if entry_prefix_ended {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::LocalStorageAfterEntryInstruction,
                        spanned.source_span,
                    ));
                }
            } else if block.id == function.entry {
                entry_prefix_ended = true;
            }
        }
    }

    if has_local_storage {
        for block in &function.blocks {
            let reenters_entry = match &block.terminator.terminator {
                VirTerminator::Jump { target } => target.block == function.entry,
                VirTerminator::Branch {
                    then_target,
                    else_target,
                    ..
                } => then_target.block == function.entry || else_target.block == function.entry,
                VirTerminator::Return { .. } => false,
            };
            if reenters_entry {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::LocalStorageEntryReentered,
                    block.terminator.source_span,
                ));
            }
        }
    }

    Ok(())
}

fn collect_definitions(
    memory: &VirMemorySchema,
    function: &VirFunction,
) -> Result<BTreeMap<VirValueId, VirType>, VirValidationError> {
    let mut definitions = BTreeMap::new();
    for block in &function.blocks {
        for parameter in &block.parameters {
            validate_declared_type(
                memory,
                function,
                Some(block),
                parameter.ty,
                block.source_span,
            )?;
            insert_definition(
                function,
                block,
                &mut definitions,
                *parameter,
                block.source_span,
            )?;
        }
        for spanned in &block.instructions {
            let mut duplicate = None;
            let mut invalid_type = None;
            spanned.instruction.visit_results(|result| {
                if let VirType::Pointer { access } = result.ty
                    && !memory.resolves_access(access)
                {
                    invalid_type.get_or_insert(access);
                }
                if definitions.insert(result.id, result.ty).is_some() {
                    duplicate.get_or_insert(result.id);
                }
            });
            if let Some(access) = invalid_type {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidMemoryAccess(access),
                    spanned.source_span,
                ));
            }
            if let Some(value) = duplicate {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::DuplicateValue(value),
                    spanned.source_span,
                ));
            }
        }
    }
    Ok(definitions)
}

fn validate_declared_type(
    memory: &VirMemorySchema,
    function: &VirFunction,
    block: Option<&VirBasicBlock>,
    ty: VirType,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let VirType::Pointer { access } = ty else {
        return Ok(());
    };
    if memory.resolves_access(access) {
        return Ok(());
    }
    let kind = VirValidationErrorKind::InvalidMemoryAccess(access);
    Err(match block {
        Some(block) => block_error(function, block, kind, source_span),
        None => function_error(function, kind, source_span),
    })
}

fn insert_definition(
    function: &VirFunction,
    block: &VirBasicBlock,
    definitions: &mut BTreeMap<VirValueId, VirType>,
    value: VirValue,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    if definitions.insert(value.id, value.ty).is_some() {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::DuplicateValue(value.id),
            source_span,
        ));
    }
    Ok(())
}

fn validate_block(
    function: &VirFunction,
    block: &VirBasicBlock,
    blocks: &BTreeMap<VirBlockId, &VirBasicBlock>,
    definitions: &BTreeMap<VirValueId, VirType>,
    loans: &LoanValidationContext<'_>,
) -> Result<(), VirValidationError> {
    let mut available: BTreeMap<_, _> = block
        .parameters
        .iter()
        .map(|parameter| (parameter.id, parameter.ty))
        .collect();

    for (instruction_index, spanned) in block.instructions.iter().enumerate() {
        if !span_contains(block.source_span, spanned.source_span) {
            return Err(block_error(
                function,
                block,
                VirValidationErrorKind::SpanOutsideParent,
                spanned.source_span,
            ));
        }
        validate_instruction(
            function,
            block,
            instruction_index,
            spanned,
            definitions,
            &available,
            loans,
        )?;
        spanned
            .instruction
            .visit_results(|result| _ = available.insert(result.id, result.ty));
    }

    if !span_contains(block.source_span, block.terminator.source_span) {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::SpanOutsideParent,
            block.terminator.source_span,
        ));
    }
    match &block.terminator.terminator {
        VirTerminator::Jump { target } => validate_target(
            function,
            block,
            target,
            blocks,
            definitions,
            &available,
            block.terminator.source_span,
        ),
        VirTerminator::Branch {
            condition,
            then_target,
            else_target,
        } => {
            expect_type(
                function,
                block,
                definitions,
                &available,
                *condition,
                VirType::Bool,
                "branch condition",
                block.terminator.source_span,
            )?;
            validate_target(
                function,
                block,
                then_target,
                blocks,
                definitions,
                &available,
                block.terminator.source_span,
            )?;
            validate_target(
                function,
                block,
                else_target,
                blocks,
                definitions,
                &available,
                block.terminator.source_span,
            )
        }
        VirTerminator::Return { values } => check_operand_types(
            function,
            block,
            "function return values",
            &function.signature.results,
            values,
            definitions,
            &available,
            block.terminator.source_span,
        ),
    }
}

fn validate_instruction(
    function: &VirFunction,
    block: &VirBasicBlock,
    instruction_index: usize,
    spanned: &SpannedVirInstruction,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    loans: &LoanValidationContext<'_>,
) -> Result<(), VirValidationError> {
    let memory = &loans.unit.memory;
    let span = spanned.source_span;
    match &spanned.instruction {
        VirInstruction::PointerCompare {
            result,
            left,
            right,
            ..
        }
        | VirInstruction::PointerDistance {
            result,
            begin: left,
            end: right,
        } => {
            let ty = available_type(function, block, definitions, available, *left, span)?;
            if !matches!(ty, VirType::Pointer { .. }) {
                return Err(type_error(
                    function,
                    block,
                    "pointer relation operand",
                    VirType::Pointer {
                        access: VirMemoryAccess::core_u64(),
                    },
                    ty,
                    span,
                ));
            }
            if let VirType::Pointer { access } = ty
                && memory
                    .layout(access.layout)
                    .is_none_or(|layout| layout.size_bytes == 0)
            {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidMemoryAccess(access),
                    span,
                ));
            }
            expect_type(
                function,
                block,
                definitions,
                available,
                *right,
                ty,
                "pointer relation operand",
                span,
            )?;
            let expected = if matches!(&spanned.instruction, VirInstruction::PointerCompare { .. })
            {
                VirType::Bool
            } else {
                VirType::U64
            };
            expect_result_type(
                function,
                block,
                *result,
                expected,
                "pointer relation result",
                span,
            )
        }
        VirInstruction::Constant { result, value } => expect_result_type(
            function,
            block,
            *result,
            value.ty(),
            "constant result",
            span,
        ),
        VirInstruction::WordAdd {
            result,
            left,
            right,
        } => {
            expect_result_type(function, block, *result, VirType::U64, "add result", span)?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *left,
                VirType::U64,
                "add left operand",
                span,
            )?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *right,
                VirType::U64,
                "add right operand",
                span,
            )
        }
        VirInstruction::Compare {
            result,
            left,
            right,
            ..
        } => {
            expect_result_type(
                function,
                block,
                *result,
                VirType::Bool,
                "comparison result",
                span,
            )?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *left,
                VirType::U64,
                "comparison left operand",
                span,
            )?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *right,
                VirType::U64,
                "comparison right operand",
                span,
            )
        }
        VirInstruction::Allocate {
            pointer_result,
            permission_result,
            size_bytes,
            alignment,
            element,
            ..
        } => {
            if *alignment == 0 || !alignment.is_power_of_two() {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidAlignment(*alignment),
                    span,
                ));
            }
            if !memory.resolves_access(*element) {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidMemoryAccess(*element),
                    span,
                ));
            }
            expect_result_type(
                function,
                block,
                *pointer_result,
                VirType::Pointer { access: *element },
                "allocation pointer result",
                span,
            )?;
            expect_result_type(
                function,
                block,
                *permission_result,
                VirType::Permission,
                "allocation permission result",
                span,
            )?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *size_bytes,
                VirType::U64,
                "allocation size",
                span,
            )
        }
        VirInstruction::LocalStorage {
            pointer_result,
            permission_result,
            access,
        } => {
            let shape = memory.object_shape(*access).map_err(|error| {
                block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidLocalStorageShape(error.kind().clone()),
                    span,
                )
            })?;
            if shape.size_bytes() == 0 {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::ZeroSizedLocalStorage,
                    span,
                ));
            }
            expect_result_type(
                function,
                block,
                *pointer_result,
                VirType::Pointer { access: *access },
                "local storage pointer result",
                span,
            )?;
            expect_result_type(
                function,
                block,
                *permission_result,
                VirType::Permission,
                "local storage permission result",
                span,
            )
        }
        VirInstruction::Initialize {
            pointer,
            value,
            permission,
            access,
        }
        | VirInstruction::Write {
            pointer,
            value,
            permission,
            access,
        }
        | VirInstruction::Store {
            pointer,
            value,
            permission,
            access,
        } => {
            let scalar_type = expect_scalar_access(function, block, memory, *access, span)?;
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *pointer,
                *access,
                "write pointer",
                span,
            )?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *value,
                scalar_type,
                "write value",
                span,
            )?;
            expect_permission(function, block, definitions, available, *permission, span)
        }
        VirInstruction::Load {
            result,
            pointer,
            permission,
            access,
        } => {
            let scalar_type = expect_scalar_access(function, block, memory, *access, span)?;
            expect_result_type(function, block, *result, scalar_type, "load result", span)?;
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *pointer,
                *access,
                "load pointer",
                span,
            )?;
            expect_permission(function, block, definitions, available, *permission, span)
        }
        VirInstruction::ResourceInitialize {
            destination,
            destination_permission,
            value,
            value_permission,
            access,
        } => {
            let pointee = expect_storable_resource_access(function, block, memory, *access, span)?;
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *destination,
                *access,
                "resource initialize destination",
                span,
            )?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *value,
                VirType::Pointer { access: pointee },
                "resource initialize value",
                span,
            )?;
            expect_permission(
                function,
                block,
                definitions,
                available,
                *destination_permission,
                span,
            )?;
            expect_permission(
                function,
                block,
                definitions,
                available,
                *value_permission,
                span,
            )?;
            if destination_permission == value_permission {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::ResourcePermissionAliases,
                    span,
                ));
            }
            Ok(())
        }
        VirInstruction::ResourceTake {
            pointer_result,
            permission_result,
            source,
            source_permission,
            access,
        } => {
            let pointee = expect_storable_resource_access(function, block, memory, *access, span)?;
            expect_result_type(
                function,
                block,
                *pointer_result,
                VirType::Pointer { access: pointee },
                "resource take pointer result",
                span,
            )?;
            expect_result_type(
                function,
                block,
                *permission_result,
                VirType::Permission,
                "resource take permission result",
                span,
            )?;
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *source,
                *access,
                "resource take source",
                span,
            )?;
            expect_permission(
                function,
                block,
                definitions,
                available,
                *source_permission,
                span,
            )
        }
        VirInstruction::DropOwn {
            pointer,
            permission,
            condition,
        } => {
            expect_any_pointer(
                function,
                block,
                definitions,
                available,
                *pointer,
                "builtin drop owner pointer",
                span,
            )?;
            expect_permission(function, block, definitions, available, *permission, span)?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *condition,
                VirType::Bool,
                "builtin drop condition",
                span,
            )
        }
        VirInstruction::EnumDiscriminant {
            result,
            pointer,
            permission,
            access,
        } => {
            validate_object_effect_shape(memory, function, block, *access, span)?;
            if !matches!(memory.kind(access.ty), Some(VirMemoryTypeKind::Enum { .. })) {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidMemoryAccess(*access),
                    span,
                ));
            }
            expect_result_type(
                function,
                block,
                *result,
                VirType::U64,
                "enum discriminant result",
                span,
            )?;
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *pointer,
                *access,
                "enum discriminant pointer",
                span,
            )?;
            expect_permission(function, block, definitions, available, *permission, span)
        }
        VirInstruction::ObjectTransfer {
            destination,
            destination_permission,
            source,
            source_permission,
            access,
            ..
        } => {
            validate_object_effect_shape(memory, function, block, *access, span)?;
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *destination,
                *access,
                "object transfer destination",
                span,
            )?;
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *source,
                *access,
                "object transfer source",
                span,
            )?;
            expect_permission(
                function,
                block,
                definitions,
                available,
                *destination_permission,
                span,
            )?;
            expect_permission(
                function,
                block,
                definitions,
                available,
                *source_permission,
                span,
            )?;
            if destination == source {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::ObjectEffectAliases,
                    span,
                ));
            }
            Ok(())
        }
        VirInstruction::ObjectDeinitialize {
            pointer,
            permission,
            access,
        }
        | VirInstruction::StorageReset {
            pointer,
            permission,
            access,
        }
        | VirInstruction::ResourceStorageReset {
            pointer,
            permission,
            access,
        } => {
            validate_object_effect_shape(memory, function, block, *access, span)?;
            if matches!(&spanned.instruction, VirInstruction::StorageReset { .. })
                && !memory
                    .object_shape(*access)
                    .is_ok_and(|shape| shape.supports_storage_reset())
            {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidMemoryAccess(*access),
                    span,
                ));
            }
            if matches!(
                &spanned.instruction,
                VirInstruction::ResourceStorageReset { .. }
            ) && !memory
                .object_shape(*access)
                .is_ok_and(|shape| shape.supports_resource_storage_reset())
            {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidMemoryAccess(*access),
                    span,
                ));
            }
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *pointer,
                *access,
                "object deinitialize pointer",
                span,
            )?;
            expect_permission(function, block, definitions, available, *permission, span)?;
            Ok(())
        }
        VirInstruction::ObjectDrop {
            pointer,
            permission,
            access,
            condition,
        } => {
            let shape = memory.object_shape(*access).map_err(|_| {
                block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidMemoryAccess(*access),
                    span,
                )
            })?;
            let supported = memory
                .type_capabilities(access.ty)
                .is_some_and(|capability| {
                    capability.size == crate::SizeCapability::Sized
                        && matches!(
                            capability.drop,
                            crate::DropCapability::TrivialDrop | crate::DropCapability::BuiltinDrop
                        )
                })
                && !shape.resource_leaves().is_empty()
                && shape
                    .resource_leaves()
                    .iter()
                    .all(|leaf| leaf.kind() != VirPointerKind::Raw);
            if !supported {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidMemoryAccess(*access),
                    span,
                ));
            }
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *pointer,
                *access,
                "object drop pointer",
                span,
            )?;
            expect_permission(function, block, definitions, available, *permission, span)?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *condition,
                VirType::Bool,
                "object drop condition",
                span,
            )
        }
        VirInstruction::EnumSetDiscriminant {
            pointer,
            permission,
            access,
            variant,
            ..
        } => {
            validate_object_effect_shape(memory, function, block, *access, span)?;
            let valid_variant = matches!(
                memory.kind(access.ty),
                Some(VirMemoryTypeKind::Enum { variants }) if variants.contains(variant)
            );
            if !valid_variant {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidEnumObjectEffect(*variant),
                    span,
                ));
            }
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *pointer,
                *access,
                "enum discriminant pointer",
                span,
            )?;
            expect_permission(function, block, definitions, available, *permission, span)?;
            Ok(())
        }
        VirInstruction::RawAddress {
            result,
            base,
            source_permission,
            raw_type,
        } => {
            let (pointee, _) = memory.raw_address_pointee(*raw_type).ok_or_else(|| {
                block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidMemoryAccess(*raw_type),
                    span,
                )
            })?;
            expect_memory_pointer(
                function,
                block,
                definitions,
                available,
                *base,
                pointee,
                "raw address source",
                span,
            )?;
            expect_result_type(
                function,
                block,
                *result,
                VirType::Pointer { access: pointee },
                "raw address result",
                span,
            )?;
            expect_permission(
                function,
                block,
                definitions,
                available,
                *source_permission,
                span,
            )
        }
        VirInstruction::PointerOffset {
            result,
            base,
            delta_bytes,
        } => {
            let pointer_type =
                available_type(function, block, definitions, available, *base, span)?;
            if !matches!(pointer_type, VirType::Pointer { .. }) {
                return Err(type_error(
                    function,
                    block,
                    "pointer offset base",
                    VirType::Pointer {
                        access: VirMemoryAccess::core_u64(),
                    },
                    pointer_type,
                    span,
                ));
            }
            expect_result_type(
                function,
                block,
                *result,
                pointer_type,
                "pointer offset result",
                span,
            )?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *delta_bytes,
                VirType::U64,
                "pointer offset delta",
                span,
            )
        }
        VirInstruction::FieldAddress {
            result,
            base,
            field,
            owner,
            field_access,
            offset_bytes,
        } => {
            expect_address_result_and_base(
                function,
                block,
                definitions,
                available,
                *result,
                *base,
                *owner,
                *field_access,
                "field address",
                span,
            )?;
            let valid = memory
                .field_subobject(*owner, *field)
                .is_some_and(|projection| {
                    projection.access() == *field_access
                        && projection.offset_bytes() == *offset_bytes
                });
            if !valid {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidFieldProjection(*field),
                    span,
                ));
            }
            Ok(())
        }
        VirInstruction::TupleElementAddress {
            result,
            base,
            index,
            owner,
            element_access,
            offset_bytes,
        } => {
            expect_address_result_and_base(
                function,
                block,
                definitions,
                available,
                *result,
                *base,
                *owner,
                *element_access,
                "tuple element address",
                span,
            )?;
            if !memory
                .subobject(*owner, &[super::VirObjectPathSegment::TupleElement(*index)])
                .is_some_and(|projection| {
                    projection.access() == *element_access
                        && projection.offset_bytes() == *offset_bytes
                })
            {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidTupleProjection(*index),
                    span,
                ));
            }
            Ok(())
        }
        VirInstruction::ObjectLeafAddress {
            result,
            base,
            owner,
            leaf,
            offset_bytes,
        } => {
            expect_address_result_and_base(
                function,
                block,
                definitions,
                available,
                *result,
                *base,
                *owner,
                *leaf,
                "object leaf address",
                span,
            )?;
            let valid = memory.object_shape(*owner).is_ok_and(|shape| {
                shape.leaves().iter().any(|candidate| {
                    candidate.access() == *leaf && candidate.bytes().start_bytes() == *offset_bytes
                })
            });
            if !valid {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidObjectLeafProjection,
                    span,
                ));
            }
            Ok(())
        }
        VirInstruction::IndexAddress {
            result,
            base,
            index,
            source,
            element,
            stride_bytes,
            bounds,
        } => {
            expect_type(
                function,
                block,
                definitions,
                available,
                *index,
                VirType::U64,
                "index address operand",
                span,
            )?;
            match bounds {
                VirIndexBounds::Array { .. } => {
                    expect_address_result_and_base(
                        function,
                        block,
                        definitions,
                        available,
                        *result,
                        *base,
                        *source,
                        *element,
                        "array index address",
                        span,
                    )?;
                }
                VirIndexBounds::Slice { length } => {
                    expect_address_result_and_base(
                        function,
                        block,
                        definitions,
                        available,
                        *result,
                        *base,
                        *element,
                        *element,
                        "slice index address",
                        span,
                    )?;
                    expect_type(
                        function,
                        block,
                        definitions,
                        available,
                        *length,
                        VirType::U64,
                        "slice index length",
                        span,
                    )?;
                }
            };
            let valid = memory.sequence(*source, *bounds).is_some_and(|sequence| {
                sequence.element() == *element && sequence.stride_bytes() == *stride_bytes
            });
            if !valid {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidIndexProjection,
                    span,
                ));
            }
            Ok(())
        }
        VirInstruction::SliceAddress {
            pointer_result,
            length_result,
            base,
            start,
            end,
            source,
            slice,
            element,
            stride_bytes,
            bounds,
        } => {
            expect_result_type(
                function,
                block,
                *pointer_result,
                VirType::Pointer { access: *element },
                "slice address pointer result",
                span,
            )?;
            expect_result_type(
                function,
                block,
                *length_result,
                VirType::U64,
                "slice address length result",
                span,
            )?;
            for (value, context) in [(*start, "slice address start"), (*end, "slice address end")] {
                expect_type(
                    function,
                    block,
                    definitions,
                    available,
                    value,
                    VirType::U64,
                    context,
                    span,
                )?;
            }
            match bounds {
                VirIndexBounds::Array { .. } => {
                    expect_memory_pointer(
                        function,
                        block,
                        definitions,
                        available,
                        *base,
                        *source,
                        "array-to-slice address base",
                        span,
                    )?;
                }
                VirIndexBounds::Slice { length } => {
                    expect_memory_pointer(
                        function,
                        block,
                        definitions,
                        available,
                        *base,
                        *element,
                        "subslice address base",
                        span,
                    )?;
                    expect_type(
                        function,
                        block,
                        definitions,
                        available,
                        *length,
                        VirType::U64,
                        "subslice address source length",
                        span,
                    )?;
                }
            };
            let valid = memory
                .slice_sequence(*source, *slice, *bounds)
                .is_some_and(|sequence| {
                    sequence.element() == *element && sequence.stride_bytes() == *stride_bytes
                });
            if !valid {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidSliceRange,
                    span,
                ));
            }
            Ok(())
        }
        VirInstruction::SliceRange {
            pointer_result,
            length_result,
            permission_result,
            base,
            permission,
            start,
            end,
            source,
            slice,
            element,
            stride_bytes,
            bounds,
        } => {
            expect_result_type(
                function,
                block,
                *pointer_result,
                VirType::Pointer { access: *element },
                "slice range pointer result",
                span,
            )?;
            expect_result_type(
                function,
                block,
                *length_result,
                VirType::U64,
                "slice range length result",
                span,
            )?;
            expect_result_type(
                function,
                block,
                *permission_result,
                VirType::Permission,
                "slice range permission result",
                span,
            )?;
            expect_permission(function, block, definitions, available, *permission, span)?;
            for (value, context) in [(*start, "slice range start"), (*end, "slice range end")] {
                expect_type(
                    function,
                    block,
                    definitions,
                    available,
                    value,
                    VirType::U64,
                    context,
                    span,
                )?;
            }
            match bounds {
                VirIndexBounds::Array { .. } => {
                    expect_memory_pointer(
                        function,
                        block,
                        definitions,
                        available,
                        *base,
                        *source,
                        "array-to-slice base",
                        span,
                    )?;
                }
                VirIndexBounds::Slice { length } => {
                    expect_memory_pointer(
                        function,
                        block,
                        definitions,
                        available,
                        *base,
                        *element,
                        "subslice base",
                        span,
                    )?;
                    expect_type(
                        function,
                        block,
                        definitions,
                        available,
                        *length,
                        VirType::U64,
                        "subslice source length",
                        span,
                    )?;
                }
            };
            let valid = memory
                .slice_sequence(*source, *slice, *bounds)
                .is_some_and(|sequence| {
                    sequence.element() == *element && sequence.stride_bytes() == *stride_bytes
                });
            if !valid {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidSliceRange,
                    span,
                ));
            }
            Ok(())
        }
        VirInstruction::Free {
            pointer,
            permission,
        } => {
            expect_any_pointer(
                function,
                block,
                definitions,
                available,
                *pointer,
                "free pointer",
                span,
            )?;
            expect_permission(function, block, definitions, available, *permission, span)
        }
        VirInstruction::PermissionSplit {
            left_result,
            right_result,
            source,
            split_at_bytes,
        } => {
            expect_result_type(
                function,
                block,
                *left_result,
                VirType::Permission,
                "permission split left result",
                span,
            )?;
            expect_result_type(
                function,
                block,
                *right_result,
                VirType::Permission,
                "permission split right result",
                span,
            )?;
            expect_permission(function, block, definitions, available, *source, span)?;
            expect_type(
                function,
                block,
                definitions,
                available,
                *split_at_bytes,
                VirType::U64,
                "permission split offset",
                span,
            )
        }
        VirInstruction::PermissionJoin {
            result,
            left,
            right,
        } => {
            expect_result_type(
                function,
                block,
                *result,
                VirType::Permission,
                "permission join result",
                span,
            )?;
            expect_permission(function, block, definitions, available, *left, span)?;
            expect_permission(function, block, definitions, available, *right, span)
        }
        VirInstruction::PermissionMove { result, source } => {
            expect_result_type(
                function,
                block,
                *result,
                VirType::Permission,
                "permission move result",
                span,
            )?;
            expect_permission(function, block, definitions, available, *source, span)
        }
        VirInstruction::LoanBegin {
            effect,
            reference_result,
            permission_result,
        } => validate_loan_instruction(
            memory,
            function,
            block,
            instruction_index,
            LoanOpcode::Begin,
            *effect,
            Some((*reference_result, *permission_result)),
            definitions,
            available,
            loans,
            span,
        ),
        VirInstruction::LoanAliasShared {
            effect,
            reference_result,
            permission_result,
        } => validate_loan_instruction(
            memory,
            function,
            block,
            instruction_index,
            LoanOpcode::AliasShared,
            *effect,
            Some((*reference_result, *permission_result)),
            definitions,
            available,
            loans,
            span,
        ),
        VirInstruction::LoanReborrow {
            effect,
            reference_result,
            permission_result,
        } => validate_loan_instruction(
            memory,
            function,
            block,
            instruction_index,
            LoanOpcode::Reborrow,
            *effect,
            Some((*reference_result, *permission_result)),
            definitions,
            available,
            loans,
            span,
        ),
        VirInstruction::LoanEnd { effect } => validate_loan_instruction(
            memory,
            function,
            block,
            instruction_index,
            LoanOpcode::End,
            *effect,
            None,
            definitions,
            available,
            loans,
            span,
        ),
        VirInstruction::LoanAliasAuthority {
            effect,
            reference_result,
            permission_result,
        } => validate_loan_authority_instruction(
            memory,
            function,
            block,
            *effect,
            true,
            Some((*reference_result, *permission_result)),
            definitions,
            available,
            span,
        ),
        VirInstruction::LoanEndAuthority { effect } => validate_loan_authority_instruction(
            memory,
            function,
            block,
            *effect,
            false,
            None,
            definitions,
            available,
            span,
        ),
        VirInstruction::LoanReborrowAuthority {
            loan,
            region,
            effect,
            reference_result,
            permission_result,
        } => {
            if !loans.unit.borrows.region(*region).is_some_and(|r| {
                r.owner == function.id && borrow_region_contains_block(r, block.id)
            }) {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::LoanEffectOutsideRegion(*loan),
                    span,
                ));
            }
            validate_loan_authority_instruction(
                memory,
                function,
                block,
                *effect,
                false,
                Some((*reference_result, *permission_result)),
                definitions,
                available,
                span,
            )
        }
        VirInstruction::Check { condition } => expect_type(
            function,
            block,
            definitions,
            available,
            *condition,
            VirType::Bool,
            "runtime check condition",
            span,
        ),
        VirInstruction::Call {
            results,
            target,
            arguments,
        } => {
            if target.symbol.is_empty() {
                return Err(block_error(
                    function,
                    block,
                    VirValidationErrorKind::EmptyCallSymbol,
                    span,
                ));
            }
            for ty in target
                .signature
                .parameters
                .iter()
                .chain(&target.signature.results)
            {
                validate_declared_type(memory, function, Some(block), *ty, span)?;
            }
            if let Some(abi) = &target.abi {
                abi.validate(memory).map_err(|error| {
                    block_error(
                        function,
                        block,
                        VirValidationErrorKind::InvalidAggregateAbi(error.kind().clone()),
                        span,
                    )
                })?;
                if abi.physical() != &target.signature {
                    return Err(block_error(
                        function,
                        block,
                        VirValidationErrorKind::InvalidAggregateAbi(
                            VirAbiErrorKind::NonCanonicalSlotMap,
                        ),
                        span,
                    ));
                }
            }
            check_operand_types(
                function,
                block,
                "call arguments",
                &target.signature.parameters,
                arguments,
                definitions,
                available,
                span,
            )?;
            check_types(
                function,
                block,
                "call results",
                &target.signature.results,
                results,
            )
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LoanOpcode {
    Begin,
    AliasShared,
    Reborrow,
    End,
}

#[allow(clippy::too_many_arguments)]
fn validate_loan_instruction(
    memory: &VirMemorySchema,
    function: &VirFunction,
    block: &VirBasicBlock,
    instruction_index: usize,
    opcode: LoanOpcode,
    effect: VirLoanEffect,
    results: Option<(VirValue, VirValue)>,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    loans: &LoanValidationContext<'_>,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let Some(region) = loans.unit.borrows.region(effect.region) else {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::InvalidLoanEffect(effect.loan),
            source_span,
        ));
    };
    if region.owner != function.id || !borrow_region_contains_block(region, block.id) {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::LoanEffectOutsideRegion(effect.loan),
            source_span,
        ));
    }

    let (pointee, reference_mutability, slice_reference) = match memory.kind(effect.reference.ty) {
        Some(VirMemoryTypeKind::Pointer {
            pointee,
            kind: VirPointerKind::Reference,
            mutability,
        }) if memory.resolves_access(effect.reference) => (*pointee, *mutability, false),
        Some(VirMemoryTypeKind::Slice {
            element,
            mutability,
        }) if memory.resolves_access(effect.reference) => (*element, *mutability, true),
        _ => {
            return Err(block_error(
                function,
                block,
                VirValidationErrorKind::InvalidLoanReference(effect.reference),
                source_span,
            ));
        }
    };
    let expected_mutability = match effect.kind {
        VirLoanKind::Shared => VirMutability::Const,
        VirLoanKind::Mutable => VirMutability::Mutable,
    };
    let Some(pointee) = memory.access(pointee) else {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::InvalidLoanReference(effect.reference),
            source_span,
        ));
    };
    let canonical_range = effect.range.len_bytes().zip(
        memory
            .layout(pointee.layout)
            .map(|layout| layout.size_bytes),
    );
    if reference_mutability != expected_mutability
        || canonical_range
            .is_none_or(|(range, pointee_size)| !slice_reference && range < pointee_size)
    {
        return Err(block_error(
            function,
            block,
            if reference_mutability != expected_mutability {
                VirValidationErrorKind::InvalidLoanReference(effect.reference)
            } else {
                VirValidationErrorKind::InvalidLoanRange(effect.loan)
            },
            source_span,
        ));
    }

    if !slice_reference {
        let abi =
            super::VirAbiSignature::classify(memory, &[], &[effect.reference]).map_err(|_| {
                block_error(
                    function,
                    block,
                    VirValidationErrorKind::InvalidLoanReference(effect.reference),
                    source_span,
                )
            })?;
        let expected_transfer = match effect.kind {
            VirLoanKind::Shared => VirInterfaceTransfer::BorrowShared,
            VirLoanKind::Mutable => VirInterfaceTransfer::BorrowMutable,
        };
        if abi.results().len() != 1
            || abi.results()[0].interface().transfer != expected_transfer
            || !abi.physical().parameters.is_empty()
            || abi.physical().results != [VirType::Pointer { access: pointee }, VirType::Permission]
        {
            return Err(block_error(
                function,
                block,
                VirValidationErrorKind::InvalidLoanReference(effect.reference),
                source_span,
            ));
        }
    }

    expect_memory_pointer(
        function,
        block,
        definitions,
        available,
        effect.source_pointer,
        pointee,
        "loan source pointer",
        source_span,
    )?;
    expect_permission(
        function,
        block,
        definitions,
        available,
        effect.source_permission,
        source_span,
    )?;
    if let Some((reference_result, permission_result)) = results {
        expect_result_type(
            function,
            block,
            reference_result,
            VirType::Pointer { access: pointee },
            "loan reference result",
            source_span,
        )?;
        expect_result_type(
            function,
            block,
            permission_result,
            VirType::Permission,
            "loan permission result",
            source_span,
        )?;
    }

    let Some(definition) = loans.definitions.get(&effect.loan).copied() else {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::MissingLoan(effect.loan),
            source_span,
        ));
    };
    if !same_loan_metadata(effect, definition.effect) {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::LoanMetadataMismatch(effect.loan),
            source_span,
        ));
    }
    let order = loans.order(block.id, instruction_index);
    if !matches!(opcode, LoanOpcode::Begin | LoanOpcode::Reborrow) && order <= definition.order {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::LoanEffectOutOfOrder(effect.loan),
            source_span,
        ));
    }

    match opcode {
        LoanOpcode::Begin if effect.parent.is_none() => Ok(()),
        LoanOpcode::AliasShared if effect.kind == VirLoanKind::Shared => Ok(()),
        LoanOpcode::Reborrow => {
            validate_reborrow_parent(function, block, effect, loans, source_span)
        }
        LoanOpcode::End => Ok(()),
        LoanOpcode::Begin | LoanOpcode::AliasShared => Err(block_error(
            function,
            block,
            VirValidationErrorKind::InvalidLoanEffect(effect.loan),
            source_span,
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_loan_authority_instruction(
    memory: &VirMemorySchema,
    function: &VirFunction,
    block: &VirBasicBlock,
    effect: super::VirLoanAuthorityEffect,
    alias: bool,
    results: Option<(VirValue, VirValue)>,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let (pointee, mutability) = match memory.kind(effect.reference.ty) {
        Some(VirMemoryTypeKind::Pointer {
            pointee,
            kind: VirPointerKind::Reference,
            mutability,
        })
        | Some(VirMemoryTypeKind::Slice {
            element: pointee,
            mutability,
        }) if memory.resolves_access(effect.reference) => (*pointee, *mutability),
        _ => {
            return Err(block_error(
                function,
                block,
                VirValidationErrorKind::InvalidLoanReference(effect.reference),
                source_span,
            ));
        }
    };
    if alias && mutability != VirMutability::Const {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::InvalidLoanReference(effect.reference),
            source_span,
        ));
    }
    let pointee = memory.access(pointee).ok_or_else(|| {
        block_error(
            function,
            block,
            VirValidationErrorKind::InvalidLoanReference(effect.reference),
            source_span,
        )
    })?;
    expect_memory_pointer(
        function,
        block,
        definitions,
        available,
        effect.source_pointer,
        pointee,
        "authority loan source pointer",
        source_span,
    )?;
    expect_permission(
        function,
        block,
        definitions,
        available,
        effect.source_permission,
        source_span,
    )?;
    if let Some((reference_result, permission_result)) = results {
        expect_result_type(
            function,
            block,
            reference_result,
            VirType::Pointer { access: pointee },
            "authority loan pointer result",
            source_span,
        )?;
        expect_result_type(
            function,
            block,
            permission_result,
            VirType::Permission,
            "authority loan permission result",
            source_span,
        )?;
        if reference_result.id == effect.source_pointer
            || permission_result.id == effect.source_permission
        {
            return Err(block_error(
                function,
                block,
                VirValidationErrorKind::InvalidLoanReference(effect.reference),
                source_span,
            ));
        }
    }
    Ok(())
}

fn validate_reborrow_parent(
    function: &VirFunction,
    block: &VirBasicBlock,
    effect: VirLoanEffect,
    loans: &LoanValidationContext<'_>,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let Some(parent) = effect
        .parent
        .and_then(|parent| loans.definitions.get(&parent).copied())
    else {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::InvalidLoanParent(effect.loan),
            source_span,
        ));
    };
    let kind_valid =
        parent.effect.kind == VirLoanKind::Mutable || effect.kind == VirLoanKind::Shared;
    let range_valid = parent.effect.range.contains(effect.range);
    let region_valid =
        borrow_region_is_subregion(loans.unit, function.id, effect.region, parent.effect.region);
    if kind_valid
        && range_valid
        && region_valid
        && parent.order < loans.definitions[&effect.loan].order
    {
        Ok(())
    } else {
        Err(block_error(
            function,
            block,
            VirValidationErrorKind::InvalidLoanParent(effect.loan),
            source_span,
        ))
    }
}

fn same_loan_metadata(left: VirLoanEffect, right: VirLoanEffect) -> bool {
    left.loan == right.loan
        && left.kind == right.kind
        && left.region == right.region
        && left.parent == right.parent
        && left.reference == right.reference
        && left.range == right.range
}

fn borrow_region_contains_block(region: &super::VirBorrowRegion, block: VirBlockId) -> bool {
    match &region.scope {
        VirBorrowRegionScope::Function => true,
        VirBorrowRegionScope::Blocks(blocks) => blocks.binary_search(&block).is_ok(),
    }
}

fn borrow_region_is_subregion(
    unit: &VirUnit,
    owner: VirFunctionId,
    subregion: VirBorrowRegionId,
    superregion: VirBorrowRegionId,
) -> bool {
    if subregion == superregion {
        return true;
    }
    let mut pending = vec![subregion];
    let mut visited = BTreeSet::new();
    while let Some(current) = pending.pop() {
        if !visited.insert(current) {
            continue;
        }
        for constraint in unit
            .borrows
            .constraints()
            .iter()
            .filter(|constraint| constraint.owner == owner && constraint.subregion == current)
        {
            if constraint.superregion == superregion {
                return true;
            }
            pending.push(constraint.superregion);
        }
    }
    false
}

fn expect_scalar_access(
    function: &VirFunction,
    block: &VirBasicBlock,
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
    source_span: ByteSpan,
) -> Result<VirType, VirValidationError> {
    let scalar = match memory.kind(access.ty) {
        Some(VirMemoryTypeKind::Bool) => Some(VirType::Bool),
        Some(VirMemoryTypeKind::Integer(
            super::VirIntegerType::U64 | super::VirIntegerType::Usize,
        )) => Some(VirType::U64),
        _ => None,
    };
    if memory.resolves_access(access)
        && let Some(scalar) = scalar
    {
        Ok(scalar)
    } else {
        Err(block_error(
            function,
            block,
            VirValidationErrorKind::InvalidMemoryAccess(access),
            source_span,
        ))
    }
}

fn expect_storable_resource_access(
    function: &VirFunction,
    block: &VirBasicBlock,
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
    source_span: ByteSpan,
) -> Result<VirMemoryAccess, VirValidationError> {
    let pointee = match memory.kind(access.ty) {
        Some(VirMemoryTypeKind::Pointer {
            pointee,
            kind: super::VirPointerKind::Own | super::VirPointerKind::Reference,
            ..
        }) => memory.access(*pointee),
        _ => None,
    };
    if memory.resolves_access(access)
        && let Some(pointee) = pointee
    {
        Ok(pointee)
    } else {
        Err(block_error(
            function,
            block,
            VirValidationErrorKind::InvalidMemoryAccess(access),
            source_span,
        ))
    }
}

fn validate_object_effect_shape(
    memory: &VirMemorySchema,
    function: &VirFunction,
    block: &VirBasicBlock,
    access: VirMemoryAccess,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    memory.object_shape(access).map(|_| ()).map_err(|error| {
        block_error(
            function,
            block,
            VirValidationErrorKind::InvalidObjectEffectShape(error.kind().clone()),
            source_span,
        )
    })
}

#[allow(clippy::too_many_arguments)]
fn validate_target(
    function: &VirFunction,
    source_block: &VirBasicBlock,
    target: &VirBlockTarget,
    blocks: &BTreeMap<VirBlockId, &VirBasicBlock>,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let Some(target_block) = blocks.get(&target.block).copied() else {
        return Err(block_error(
            function,
            source_block,
            VirValidationErrorKind::MissingTargetBlock(target.block),
            source_span,
        ));
    };
    let expected: Vec<_> = target_block
        .parameters
        .iter()
        .map(|parameter| parameter.ty)
        .collect();
    check_operand_types(
        function,
        source_block,
        "block target arguments",
        &expected,
        &target.arguments,
        definitions,
        available,
        source_span,
    )
}

fn check_types(
    function: &VirFunction,
    block: &VirBasicBlock,
    context: &'static str,
    expected: &[VirType],
    found: &[VirValue],
) -> Result<(), VirValidationError> {
    if expected.len() != found.len() {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::ArityMismatch {
                context,
                expected: expected.len(),
                found: found.len(),
            },
            block.source_span,
        ));
    }
    for (expected, found) in expected.iter().zip(found) {
        if *expected != found.ty {
            return Err(type_error(
                function,
                block,
                context,
                *expected,
                found.ty,
                block.source_span,
            ));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_operand_types(
    function: &VirFunction,
    block: &VirBasicBlock,
    context: &'static str,
    expected: &[VirType],
    found: &[VirValueId],
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    if expected.len() != found.len() {
        return Err(block_error(
            function,
            block,
            VirValidationErrorKind::ArityMismatch {
                context,
                expected: expected.len(),
                found: found.len(),
            },
            source_span,
        ));
    }
    for (expected, found) in expected.iter().zip(found) {
        expect_type(
            function,
            block,
            definitions,
            available,
            *found,
            *expected,
            context,
            source_span,
        )?;
    }
    Ok(())
}

fn expect_result_type(
    function: &VirFunction,
    block: &VirBasicBlock,
    result: VirValue,
    expected: VirType,
    context: &'static str,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    if result.ty == expected {
        Ok(())
    } else {
        Err(type_error(
            function,
            block,
            context,
            expected,
            result.ty,
            source_span,
        ))
    }
}

#[allow(clippy::too_many_arguments)]
fn expect_type(
    function: &VirFunction,
    block: &VirBasicBlock,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    value: VirValueId,
    expected: VirType,
    context: &'static str,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let found = available_type(function, block, definitions, available, value, source_span)?;
    if found == expected {
        Ok(())
    } else {
        Err(type_error(
            function,
            block,
            context,
            expected,
            found,
            source_span,
        ))
    }
}

#[allow(clippy::too_many_arguments)]
fn expect_memory_pointer(
    function: &VirFunction,
    block: &VirBasicBlock,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    value: VirValueId,
    access: VirMemoryAccess,
    context: &'static str,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    expect_type(
        function,
        block,
        definitions,
        available,
        value,
        VirType::Pointer { access },
        context,
        source_span,
    )
}

#[allow(clippy::too_many_arguments)]
fn expect_address_result_and_base(
    function: &VirFunction,
    block: &VirBasicBlock,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    result: VirValue,
    base: VirValueId,
    source_access: VirMemoryAccess,
    result_access: VirMemoryAccess,
    context: &'static str,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    expect_type(
        function,
        block,
        definitions,
        available,
        base,
        VirType::Pointer {
            access: source_access,
        },
        context,
        source_span,
    )?;
    expect_result_type(
        function,
        block,
        result,
        VirType::Pointer {
            access: result_access,
        },
        context,
        source_span,
    )
}

fn expect_any_pointer(
    function: &VirFunction,
    block: &VirBasicBlock,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    value: VirValueId,
    context: &'static str,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    let found = available_type(function, block, definitions, available, value, source_span)?;
    if matches!(found, VirType::Pointer { .. }) {
        Ok(())
    } else {
        Err(type_error(
            function,
            block,
            context,
            VirType::Pointer {
                access: VirMemoryAccess::core_u64(),
            },
            found,
            source_span,
        ))
    }
}

fn expect_permission(
    function: &VirFunction,
    block: &VirBasicBlock,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    value: VirValueId,
    source_span: ByteSpan,
) -> Result<(), VirValidationError> {
    expect_type(
        function,
        block,
        definitions,
        available,
        value,
        VirType::Permission,
        "permission operand",
        source_span,
    )
}

fn available_type(
    function: &VirFunction,
    block: &VirBasicBlock,
    definitions: &BTreeMap<VirValueId, VirType>,
    available: &BTreeMap<VirValueId, VirType>,
    value: VirValueId,
    source_span: ByteSpan,
) -> Result<VirType, VirValidationError> {
    if let Some(ty) = available.get(&value) {
        return Ok(*ty);
    }
    let kind = if definitions.contains_key(&value) {
        VirValidationErrorKind::ValueNotAvailableInBlock(value)
    } else {
        VirValidationErrorKind::UndefinedValue(value)
    };
    Err(block_error(function, block, kind, source_span))
}

fn type_error(
    function: &VirFunction,
    block: &VirBasicBlock,
    context: &'static str,
    expected: VirType,
    found: VirType,
    source_span: ByteSpan,
) -> VirValidationError {
    block_error(
        function,
        block,
        VirValidationErrorKind::TypeMismatch {
            context,
            expected,
            found,
        },
        source_span,
    )
}

fn program_error(kind: VirValidationErrorKind) -> VirValidationError {
    VirValidationError {
        kind,
        function: None,
        block: None,
        source_span: None,
    }
}

fn function_error(
    function: &VirFunction,
    kind: VirValidationErrorKind,
    source_span: ByteSpan,
) -> VirValidationError {
    VirValidationError {
        kind,
        function: Some(function.id),
        block: None,
        source_span: Some(source_span),
    }
}

fn block_error(
    function: &VirFunction,
    block: &VirBasicBlock,
    kind: VirValidationErrorKind,
    source_span: ByteSpan,
) -> VirValidationError {
    VirValidationError {
        kind,
        function: Some(function.id),
        block: Some(block.id),
        source_span: Some(source_span),
    }
}

const fn span_contains(parent: ByteSpan, child: ByteSpan) -> bool {
    parent.start() <= child.start() && child.end() <= parent.end()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vir::{VirFunctionId, VirMemorySchema, VirUnit};

    fn empty_runtime_unit() -> VirUnit {
        VirUnit::from_runtime(
            VirMemorySchema::core_u64(),
            VirFunctionId::new(0),
            Vec::new(),
        )
    }

    #[test]
    fn an_empty_runtime_still_rejects_before_contract_validation() {
        let unit = empty_runtime_unit();
        assert_eq!(
            unit.validate().expect_err("runtime is empty").kind(),
            &VirValidationErrorKind::EmptyProgram
        );
    }
}
