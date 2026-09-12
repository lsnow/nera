#[cfg(test)]
use super::relation::kernel::object_non_overlap_status;
use super::relation::kernel::{
    add_pointer_intervals, bound_le_status, interval_le_status, object_alignment_status,
    object_bounds_status, scale_pointer_interval, symbolic_bound,
};
use super::relation::range::interval_coverage as permission_coverage_status;
use super::relation::{
    RelationComparison, RelationTerm,
    difference::{DifferenceLimits, DifferencePremise, word},
};
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

mod access;
mod call;
mod domain;
mod error;
mod obligation;
#[cfg(test)]
mod tests;

use crate::VirPointerDomain;
use access::{ObjectAccessFacts, PermissionAccessContext};
pub(super) use call::ContractTransferContext;
pub(super) use call::{aggregate_abi_payload_status, install_aggregate_abi_payloads};
use domain::pointer_range;
pub use error::TransferError;
pub use obligation::{
    InstructionSequenceTransfer, InstructionTransfer, ObligationStatus, ResourceObligation,
    ResourceObligationKind,
};

use crate::{
    ByteSpan, SpannedVirInstruction, VirBorrowEnvironment, VirCallTarget, VirConstant,
    VirContractId, VirFunctionId, VirIndexBounds, VirInstruction, VirIntegerPredicate,
    VirLoanAuthorityEffect, VirLoanEffect, VirLoanId, VirLoanKind, VirMemoryAccess,
    VirMemorySchema, VirMemoryTypeKind, VirMutability, VirObjectByteRange,
    VirObjectDestinationMode, VirObjectPathSegment, VirObjectResourceLeaf, VirObjectShape,
    VirObjectSourceMode, VirPointerKind, VirRegionId, VirSpecClauseId, VirType, VirValue,
    VirValueId, VirVariantId,
};

use super::contract::{
    ContractApplicationError, ContractFactOrigin, InstantiatedContracts, apply_postconditions,
    check_preconditions,
};
use super::resource::{
    AbstractAllocation, AbstractAllocationError, AbstractAllocationId, AbstractBool,
    AbstractByteRange, AbstractLoan, AbstractObjectOffsets, AbstractPermission, AbstractPointer,
    AbstractProvenance, AbstractValue, AccessPermission, ActiveVariantState, AffineExpression,
    ByteRange, ByteSet, EnumDiscriminantFact, FreeCapability, GuaranteedAlignment,
    InitializationClass, LivenessState, LoanActivity, LoanPrecisionLoss, MemoryFootprint,
    MovePathState, ObjectStateKey, OwnershipState, PathFact, PermissionAuthority,
    PermissionAvailability, ResourcePayloadKey, ResourceState, ResourceStateDefinitionError,
    SymbolicRangeBound, TypedResourcePayload, U64Interval,
};

/// VIR v0 memory accesses operate on one 64-bit word.
pub const VIR_V0_WORD_BYTES: u64 = 8;

/// Allocation limit shared with the frozen Core0 semantics and default interpreter.
pub const VIR_V0_MAX_ALLOCATION_BYTES: u64 = 4096;

/// Applies one deterministic VIR instruction transfer.
///
/// User memory-safety failures are obligations, not `TransferError`. Errors are
/// reserved for contradictions between validated VIR and the abstract state.
pub fn transfer_instruction(
    input: &ResourceState,
    instruction: &SpannedVirInstruction,
) -> Result<InstructionTransfer, TransferError> {
    let memory = VirMemorySchema::core_u64();
    transfer_instruction_with_memory(input, instruction, &memory)
}

/// Applies one transfer using the program's canonical memory schema.
pub fn transfer_instruction_with_memory(
    input: &ResourceState,
    instruction: &SpannedVirInstruction,
    memory: &VirMemorySchema,
) -> Result<InstructionTransfer, TransferError> {
    if !input.path_condition().is_reachable() {
        return Ok(InstructionTransfer {
            cases: None,
            queries: Some(Vec::new()),
            state: input.clone(),
            obligations: Vec::new(),
        });
    }

    let mut transfer =
        TransferBuilder::new(input.clone(), instruction.source_span, memory, None, None);
    transfer.apply(&instruction.instruction)?;
    Ok(transfer.finish())
}

/// Applies one loan-aware transfer from a validated function context.
pub(super) fn transfer_instruction_with_loans_and_memory(
    input: &ResourceState,
    instruction: &SpannedVirInstruction,
    memory: &VirMemorySchema,
    relation_limits: DifferenceLimits,
    loan_context: LoanTransferContext<'_>,
) -> Result<InstructionTransfer, TransferError> {
    if !input.path_condition().is_reachable() {
        return Ok(InstructionTransfer {
            cases: None,
            queries: Some(Vec::new()),
            state: input.clone(),
            obligations: Vec::new(),
        });
    }
    let mut transfer = TransferBuilder::new(
        input.clone(),
        instruction.source_span,
        memory,
        None,
        Some(loan_context),
    );
    transfer.relation_limits = relation_limits;
    transfer.apply(&instruction.instruction)?;
    Ok(transfer.finish())
}

/// Applies one contract-aware transfer using the program's canonical schema.
pub(super) fn transfer_instruction_with_contracts_and_memory(
    input: &ResourceState,
    instruction: &SpannedVirInstruction,
    context: ContractTransferContext<'_>,
    memory: &VirMemorySchema,
    relation_limits: DifferenceLimits,
    loan_context: LoanTransferContext<'_>,
) -> Result<InstructionTransfer, TransferError> {
    if !input.path_condition().is_reachable() {
        return Ok(InstructionTransfer {
            cases: None,
            queries: Some(Vec::new()),
            state: input.clone(),
            obligations: Vec::new(),
        });
    }
    let mut transfer = TransferBuilder::new(
        input.clone(),
        instruction.source_span,
        memory,
        Some(context),
        Some(loan_context),
    );
    transfer.relation_limits = relation_limits;
    transfer.apply(&instruction.instruction)?;
    Ok(transfer.finish())
}

/// Applies stage-5.2 transfer to a straight-line VIR instruction sequence.
///
/// Terminators, edge argument renaming and CFG fixed points are composed by
/// the stage-5.3 CFG analyzer.
pub fn transfer_instruction_sequence(
    input: &ResourceState,
    instructions: &[SpannedVirInstruction],
) -> Result<InstructionSequenceTransfer, TransferError> {
    let memory = VirMemorySchema::core_u64();
    transfer_instruction_sequence_with_memory(input, instructions, &memory)
}

/// Applies a straight-line transfer using the program's canonical memory schema.
pub fn transfer_instruction_sequence_with_memory(
    input: &ResourceState,
    instructions: &[SpannedVirInstruction],
    memory: &VirMemorySchema,
) -> Result<InstructionSequenceTransfer, TransferError> {
    let mut state = input.clone();
    let mut obligations = Vec::new();
    for instruction in instructions {
        let result = transfer_instruction_with_memory(&state, instruction, memory)?;
        state = result.state;
        obligations.extend(result.obligations);
    }
    Ok(InstructionSequenceTransfer { state, obligations })
}

struct TransferBuilder<'environment> {
    cases: Option<Vec<ResourceState>>,
    relations: TransferRelations,
    relation_limits: DifferenceLimits,
    state: ResourceState,
    obligations: Vec<ResourceObligation>,
    source_span: ByteSpan,
    memory: &'environment VirMemorySchema,
    contract_context: Option<ContractTransferContext<'environment>>,
    loan_context: Option<LoanTransferContext<'environment>>,
}

#[derive(Clone, Copy)]
pub(super) struct LoanTransferLimits {
    pub max_region_pairs: usize,
    pub max_active_loans: usize,
    pub max_aliases_per_loan: usize,
    pub max_region_constraints: usize,
    pub max_reborrow_depth: usize,
}

#[derive(Clone, Copy)]
pub(super) struct LoanTransferContext<'environment> {
    pub borrows: &'environment VirBorrowEnvironment,
    pub function: VirFunctionId,
    pub limits: LoanTransferLimits,
}

struct TransferRelations {
    queries: super::relation::audit::QueryLog,
    used: std::cell::Cell<usize>,
    limit: usize,
}
impl TransferRelations {
    fn charge(&self) -> bool {
        let Some(next) = self.used.get().checked_add(1) else {
            return false;
        };
        self.used.set(next);
        next <= self.limit
    }
}

#[derive(Clone, Copy)]
struct AddressAccess {
    source: VirMemoryAccess,
    result: VirMemoryAccess,
}

#[derive(Clone, Copy)]
struct SliceAddressFacts {
    allocation_id: Option<AbstractAllocationId>,
    source_range: AbstractByteRange,
    selected_range: AbstractByteRange,
    mutable: bool,
}

#[derive(Clone)]
struct EnumSite {
    path: Vec<VirObjectPathSegment>,
    access: VirMemoryAccess,
    offset_bytes: u64,
    tag: ByteRange,
    variants: BTreeSet<VirVariantId>,
}

struct ActiveObjectMask {
    possible_value_bytes: ByteSet,
    guaranteed_value_bytes: ByteSet,
    possible_resource_leaves: Vec<VirObjectResourceLeaf>,
    guaranteed_resource_leaves: Vec<VirObjectResourceLeaf>,
    sites: Vec<(EnumSite, ActiveVariantState, ObligationStatus)>,
}

#[derive(Clone, Copy)]
struct ObjectTransferEffect {
    destination: VirValueId,
    destination_permission: VirValueId,
    source: VirValueId,
    source_permission: VirValueId,
    access: VirMemoryAccess,
    destination_mode: VirObjectDestinationMode,
    source_mode: VirObjectSourceMode,
}

impl<'environment> TransferBuilder<'environment> {
    fn range_contains(
        &self,
        outer: AbstractByteRange,
        inner: AbstractByteRange,
    ) -> ObligationStatus {
        self.relations
            .queries
            .contained(&self.state, outer, inner, self.relation_limits)
    }
    fn borrow_footprint(
        &self,
        effect: VirLoanEffect,
        pointer: AbstractPointer,
        envelope: ByteRange,
    ) -> Option<MemoryFootprint> {
        let access = reference_pointee(self.memory, effect.reference).ok()?;
        let stride_bytes = self.memory.object_shape(access).ok()?.size_bytes();
        if matches!(
            self.memory.kind(effect.reference.ty),
            Some(VirMemoryTypeKind::Slice { .. })
        ) {
            return pointer.slice_footprint().filter(|f| {
                f.provenance == pointer.provenance()
                    && f.access == access
                    && f.stride_bytes == stride_bytes
            });
        }
        let start = symbolic_bound(pointer.offset_bytes(), pointer.offset_expression());
        let range = start
            .and_then(|start| {
                start
                    .checked_add_constant(stride_bytes)
                    .map(|end| AbstractByteRange::from_bounds(start, end))
            })
            .unwrap_or(AbstractByteRange::Unknown);
        Some(MemoryFootprint {
            provenance: pointer.provenance(),
            access,
            stride_bytes,
            range,
            envelope: access_envelope(pointer.offset_bytes(), stride_bytes).unwrap_or(envelope),
        })
    }

    fn compare_words(
        &self,
        comparison: RelationComparison,
        left: RelationTerm,
        right: RelationTerm,
    ) -> ObligationStatus {
        self.relations
            .queries
            .compare(&self.state, comparison, left, right, self.relation_limits)
    }

    fn new(
        mut state: ResourceState,
        source_span: ByteSpan,
        memory: &'environment VirMemorySchema,
        contract_context: Option<ContractTransferContext<'environment>>,
        loan_context: Option<LoanTransferContext<'environment>>,
    ) -> Self {
        state.reduce_initialization_prefixes();
        Self {
            cases: None,
            relation_limits: DifferenceLimits::default(),
            relations: TransferRelations {
                queries: super::relation::audit::QueryLog::default(),
                used: std::cell::Cell::new(0),
                limit: loan_context.map_or(256, |c| c.limits.max_region_pairs),
            },
            state,
            obligations: Vec::new(),
            source_span,
            memory,
            contract_context,
            loan_context,
        }
    }

    fn finish(mut self) -> InstructionTransfer {
        if self
            .obligations
            .iter()
            .any(|obligation| obligation.status == ObligationStatus::Refuted)
        {
            self.state = ResourceState::unreachable();
            self.cases = None;
        }
        InstructionTransfer {
            cases: self.cases,
            queries: self.relations.queries.finish(),
            state: self.state,
            obligations: self.obligations,
        }
    }

    fn require(&mut self, kind: ResourceObligationKind, status: ObligationStatus) {
        self.obligations
            .push(ResourceObligation::new(kind, status, self.source_span));
    }

    fn instance_failure(
        &mut self,
        error: ResourceStateDefinitionError,
    ) -> Result<(), TransferError> {
        let allocation = match error {
            ResourceStateDefinitionError::AllocationInstanceStillReferenced(id) => Some(id),
            ResourceStateDefinitionError::AllocationInstanceBudget => None,
            other => return Err(other.into()),
        };
        self.require(
            ResourceObligationKind::AllocationInstanceFresh { allocation },
            ObligationStatus::Unknown,
        );
        Ok(())
    }

    fn define(&mut self, value: VirValue, fact: AbstractValue) -> Result<(), TransferError> {
        if !abstract_value_matches_type(fact, value.ty) {
            return Err(TransferError::ResultTypeMismatch {
                value: value.id,
                declared: value.ty,
                abstract_type: abstract_value_type_or(fact, value.ty),
            });
        }
        self.state.define_value(value.id, fact)?;
        if matches!(value.ty, VirType::U64) {
            self.state
                .set_word_expression(value.id, AffineExpression::identity(value.id));
        }
        Ok(())
    }

    fn set_word_expression(&mut self, value: VirValueId, expression: Option<AffineExpression>) {
        if let Some(expression) = expression {
            self.state.set_word_expression(value, expression);
        } else {
            self.state.clear_word_expression(value);
        }
    }

    fn set_pointer_object_offsets(
        &mut self,
        value: VirValueId,
        offsets: AbstractObjectOffsets,
        expected_access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        match self.state.value_mut(value) {
            Some(AbstractValue::Pointer(pointer)) => {
                *pointer = pointer.with_object_offsets(offsets);
                Ok(())
            }
            Some(found) => Err(TransferError::AbstractValueTypeMismatch {
                value,
                expected: VirType::Pointer {
                    access: expected_access,
                },
                found: abstract_value_type(*found),
            }),
            None => Ok(()),
        }
    }

    fn apply(&mut self, instruction: &VirInstruction) -> Result<(), TransferError> {
        if let Some(context) = self.contract_context.and_then(|c| c.summary) {
            context.observe(&self.state, instruction, self.memory);
        }
        self.relations.used.set(0);
        let result = match instruction {
            VirInstruction::PointerCompare {
                result,
                predicate,
                left,
                right,
            } => self.pointer_compare(*result, *predicate, *left, *right),
            VirInstruction::PointerDistance { result, begin, end } => {
                self.pointer_distance(*result, *begin, *end)
            }
            VirInstruction::Constant { result, value } => {
                let fact = match value {
                    VirConstant::U64(value) => AbstractValue::U64(U64Interval::exact(*value)),
                    VirConstant::Bool(true) => AbstractValue::Bool(AbstractBool::True),
                    VirConstant::Bool(false) => AbstractValue::Bool(AbstractBool::False),
                };
                self.define(*result, fact)?;
                if let VirConstant::U64(value) = value {
                    self.set_word_expression(result.id, Some(AffineExpression::constant(*value)));
                }
                Ok(())
            }
            VirInstruction::WordAdd {
                result,
                left,
                right,
            } => {
                let left_interval = word_fact(&self.state, *left)?;
                let right_interval = word_fact(&self.state, *right)?;
                let expression = left_interval
                    .upper()
                    .checked_add(right_interval.upper())
                    .and_then(|_| {
                        word_expression(&self.state, *left, left_interval)
                            .zip(word_expression(&self.state, *right, right_interval))
                            .and_then(|(left, right)| left.checked_add(right))
                    });
                self.define(
                    *result,
                    AbstractValue::U64(add_word_intervals(left_interval, right_interval)),
                )?;
                self.set_word_expression(result.id, expression);
                // Establish mathematical addition only from an independent
                // no-wrap check on the actual pre-operation intervals.
                if left_interval
                    .upper()
                    .checked_add(right_interval.upper())
                    .is_some()
                {
                    let equation = right_interval
                        .exact_value()
                        .map(|n| (*left, n))
                        .or_else(|| left_interval.exact_value().map(|n| (*right, n)));
                    if let Some((operand, offset)) = equation {
                        self.state.learn_relations(
                            &[DifferencePremise::EqualOffset {
                                left: word(result.id),
                                right: word(operand),
                                offset: i128::from(offset),
                            }],
                            self.relation_limits,
                        );
                    }
                }
                Ok(())
            }
            VirInstruction::Compare {
                result,
                predicate,
                left,
                right,
            } => {
                let left_interval = word_fact(&self.state, *left)?;
                let right_interval = word_fact(&self.state, *right)?;
                let fact = PathFact::comparison(*predicate, *left, *right);
                let value = if left == right {
                    compare_same_value(*predicate)
                } else if self.state.path_condition().implies(fact) {
                    AbstractBool::True
                } else if self.state.path_condition().implies(fact.negated()) {
                    AbstractBool::False
                } else {
                    compare_intervals(*predicate, left_interval, right_interval)
                };
                self.define(*result, AbstractValue::Bool(value))
            }
            VirInstruction::Allocate {
                pointer_result,
                permission_result,
                size_bytes,
                alignment,
                region,
                element,
                ..
            } => self.allocate(
                *pointer_result,
                *permission_result,
                *size_bytes,
                *alignment,
                *region,
                *element,
            ),
            VirInstruction::LocalStorage {
                pointer_result,
                permission_result,
                access,
            } => self.local_storage(*pointer_result, *permission_result, *access),
            VirInstruction::Initialize {
                pointer,
                value,
                permission,
                access,
            } => {
                scalar_fact(self.memory, &self.state, *value, *access)?;
                self.memory_access(
                    *pointer,
                    *permission,
                    AccessPermission::Write,
                    InitializationRequirement::Uninitialized,
                    MemoryEffect::WriteValue,
                    *access,
                )
            }
            VirInstruction::Write {
                pointer,
                value,
                permission,
                access,
            } => {
                scalar_fact(self.memory, &self.state, *value, *access)?;
                self.memory_access(
                    *pointer,
                    *permission,
                    AccessPermission::Write,
                    InitializationRequirement::None,
                    MemoryEffect::WriteValue,
                    *access,
                )
            }
            VirInstruction::Load {
                result,
                pointer,
                permission,
                access,
            } => {
                self.memory_access(
                    *pointer,
                    *permission,
                    AccessPermission::Read,
                    InitializationRequirement::Initialized,
                    MemoryEffect::None,
                    *access,
                )?;
                let value = match self.memory.kind(access.ty) {
                    Some(crate::VirMemoryTypeKind::Bool) => {
                        AbstractValue::Bool(AbstractBool::Unknown)
                    }
                    Some(crate::VirMemoryTypeKind::Integer(
                        crate::VirIntegerType::U64 | crate::VirIntegerType::Usize,
                    )) => AbstractValue::U64(U64Interval::unknown()),
                    _ => return Err(TransferError::InvalidValidatedMemoryAccess(*access)),
                };
                self.define(*result, value)
            }
            VirInstruction::EnumDiscriminant {
                result,
                pointer,
                permission,
                access,
            } => self.enum_discriminant(*result, *pointer, *permission, *access),
            VirInstruction::Store {
                pointer,
                value,
                permission,
                access,
            } => {
                scalar_fact(self.memory, &self.state, *value, *access)?;
                self.memory_access(
                    *pointer,
                    *permission,
                    AccessPermission::Write,
                    InitializationRequirement::Initialized,
                    MemoryEffect::WriteValue,
                    *access,
                )
            }
            VirInstruction::ResourceInitialize {
                destination,
                destination_permission,
                value,
                value_permission,
                access,
            } => self.resource_initialize(
                *destination,
                *destination_permission,
                *value,
                *value_permission,
                *access,
            ),
            VirInstruction::ResourceTake {
                pointer_result,
                permission_result,
                source,
                source_permission,
                access,
            } => self.resource_take(
                *pointer_result,
                *permission_result,
                *source,
                *source_permission,
                *access,
            ),
            VirInstruction::DropOwn {
                pointer,
                permission,
                condition,
            } => self.drop_own(*pointer, *permission, *condition),
            VirInstruction::ObjectTransfer {
                destination,
                destination_permission,
                source,
                source_permission,
                access,
                destination_mode,
                source_mode,
            } => self.object_transfer(ObjectTransferEffect {
                destination: *destination,
                destination_permission: *destination_permission,
                source: *source,
                source_permission: *source_permission,
                access: *access,
                destination_mode: *destination_mode,
                source_mode: *source_mode,
            }),
            VirInstruction::ObjectDeinitialize {
                pointer,
                permission,
                access,
            } => self.object_deinitialize(*pointer, *permission, *access),
            VirInstruction::StorageReset {
                pointer,
                permission,
                access,
            } => {
                let object = self.object_access_facts(
                    *pointer,
                    *permission,
                    *access,
                    AccessPermission::Write,
                )?;
                let mask = active_object_mask(&object);
                self.apply_object_deinitialize(&object, &mask)
            }
            VirInstruction::ResourceStorageReset {
                pointer,
                permission,
                access,
            } => self.resource_storage_reset(*pointer, *permission, *access),
            VirInstruction::ObjectDrop {
                pointer,
                permission,
                access,
                condition,
            } => self.object_drop(*pointer, *permission, *access, *condition),
            VirInstruction::EnumSetDiscriminant {
                pointer,
                permission,
                access,
                variant,
                mode,
            } => self.enum_set_discriminant(*pointer, *permission, *access, *variant, *mode),
            VirInstruction::RawAddress {
                result,
                base,
                source_permission,
                raw_type,
            } => {
                let (access, mutability) = self
                    .memory
                    .raw_address_pointee(*raw_type)
                    .ok_or(TransferError::InvalidValidatedMemoryAccess(*raw_type))?;
                let required = if mutability == crate::VirMutability::Mutable {
                    AccessPermission::Write
                } else {
                    AccessPermission::Read
                };
                // This shared check validates storage/authority, not initialized
                // bytes or a valid pointee representation. It has no state effect.
                let object =
                    self.object_access_facts(*base, *source_permission, access, required)?;
                self.define(*result, AbstractValue::Pointer(object.pointer))
            }
            VirInstruction::PointerOffset {
                result,
                base,
                delta_bytes,
            } => self.pointer_offset(*result, *base, *delta_bytes),
            VirInstruction::FieldAddress {
                result,
                base,
                owner,
                field,
                ..
            } => self.subobject_address(
                *result,
                *base,
                self.memory
                    .field_subobject(*owner, *field)
                    .ok_or(TransferError::InvalidDerivedRange)?,
            ),
            VirInstruction::TupleElementAddress {
                result,
                base,
                owner,
                index,
                ..
            } => self.subobject_address(
                *result,
                *base,
                self.memory
                    .subobject(*owner, &[VirObjectPathSegment::TupleElement(*index)])
                    .ok_or(TransferError::InvalidDerivedRange)?,
            ),
            VirInstruction::ObjectLeafAddress {
                result,
                base,
                owner,
                leaf,
                offset_bytes,
            } => {
                self.typed_address(
                    *result,
                    *base,
                    AddressAccess {
                        source: *owner,
                        result: *leaf,
                    },
                    U64Interval::exact(*offset_bytes),
                    Some(AffineExpression::constant(*offset_bytes)),
                )?;
                if let Some(object) = self.memory.leaf_subobject(*owner, *leaf, *offset_bytes) {
                    self.set_subobject_domain(result.id, *base, &object)?;
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
                bounds: VirIndexBounds::Array { length },
            } => self.index_address(
                *result,
                *base,
                *index,
                AddressAccess {
                    source: *source,
                    result: *element,
                },
                *stride_bytes,
                *length,
            ),
            VirInstruction::IndexAddress {
                result,
                base,
                index,
                element,
                stride_bytes,
                bounds: VirIndexBounds::Slice { length },
                ..
            } => self.slice_index_address(*result, *base, *index, *length, *element, *stride_bytes),
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
            } => self
                .slice_address(
                    *pointer_result,
                    *length_result,
                    *base,
                    *start,
                    *end,
                    *source,
                    *slice,
                    *element,
                    *stride_bytes,
                    *bounds,
                )
                .map(|_| ()),
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
            } => self.slice_range(
                *pointer_result,
                *length_result,
                *permission_result,
                *base,
                *permission,
                *start,
                *end,
                *source,
                *slice,
                *element,
                *stride_bytes,
                *bounds,
            ),
            VirInstruction::Free {
                pointer,
                permission,
            } => self.free(*pointer, *permission),
            VirInstruction::PermissionSplit {
                left_result,
                right_result,
                source,
                split_at_bytes,
            } => self.permission_split(*left_result, *right_result, *source, *split_at_bytes),
            VirInstruction::PermissionJoin {
                result,
                left,
                right,
            } => self.permission_join(*result, *left, *right),
            VirInstruction::PermissionMove { result, source } => {
                self.permission_move(*result, *source)
            }
            VirInstruction::LoanBegin {
                effect,
                reference_result,
                permission_result,
            } => self.loan_begin(*effect, *reference_result, *permission_result),
            VirInstruction::LoanAliasShared {
                effect,
                reference_result,
                permission_result,
            } => self.loan_alias_shared(*effect, *reference_result, *permission_result),
            VirInstruction::LoanReborrow {
                effect,
                reference_result,
                permission_result,
            } => self.loan_reborrow(*effect, *reference_result, *permission_result),
            VirInstruction::LoanEnd { effect } => self.loan_end(*effect),
            VirInstruction::LoanAliasAuthority {
                effect,
                reference_result,
                permission_result,
            } => self.loan_alias_authority(*effect, *reference_result, *permission_result),
            VirInstruction::LoanEndAuthority { effect } => self.loan_end_authority(*effect),
            VirInstruction::LoanReborrowAuthority {
                loan,
                region,
                effect,
                reference_result,
                permission_result,
            } => self.loan_reborrow_authority(
                *loan,
                *region,
                *effect,
                *reference_result,
                *permission_result,
            ),
            VirInstruction::Check { condition } => self.check(*condition),
            VirInstruction::Call {
                results,
                target,
                arguments,
            } => self.call(results, target, arguments),
        };
        let queries = self.relations.used.get();
        if queries > 0 {
            self.require(
                ResourceObligationKind::LoanPairQueriesWithinBudget {
                    queries,
                    limit: self.relations.limit,
                },
                if queries <= self.relations.limit {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
        }
        result
    }

    fn allocate(
        &mut self,
        pointer_result: VirValue,
        permission_result: VirValue,
        size_value: VirValueId,
        alignment: u64,
        region: VirRegionId,
        element: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let size = word_fact(&self.state, size_value)?;
        let nonzero = if size.lower() > 0 {
            ObligationStatus::Proven
        } else if size.upper() == 0 {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::AllocationSizeNonZero { size },
            nonzero,
        );

        let within_limit = if size.upper() <= VIR_V0_MAX_ALLOCATION_BYTES {
            ObligationStatus::Proven
        } else if size.lower() > VIR_V0_MAX_ALLOCATION_BYTES {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::AllocationSizeWithinLimit {
                size,
                limit: VIR_V0_MAX_ALLOCATION_BYTES,
            },
            within_limit,
        );

        let exact = size.exact_value();
        self.require(
            ResourceObligationKind::AllocationExtentExact { size },
            if exact.is_some() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        );
        let allocation_id = AbstractAllocationId::vir_allocation_site(pointer_result.id);
        if let Some(size_bytes) =
            exact.filter(|size| *size > 0 && *size <= VIR_V0_MAX_ALLOCATION_BYTES)
        {
            let mut allocation = AbstractAllocation::new(region, size_bytes, alignment)?;
            let shape = self
                .memory
                .object_shape(element)
                .map_err(|_| TransferError::InvalidValidatedMemoryAccess(element))?;
            prepare_repeated_object_state(&mut allocation, &shape)?;
            allocation.seed_initialization_prefixes(self.memory, &shape);
            // Typed allocation creates empty storage authority, never a valid
            // pointee value. Resource absence is known independently of bytes.
            if shape.size_bytes() != 0 && size_bytes % shape.size_bytes() == 0 {
                for base in (0..size_bytes).step_by(shape.size_bytes() as usize) {
                    for leaf in shape.resource_leaves() {
                        let _ = allocation.set_resource_payload(
                            ResourcePayloadKey::new(
                                base + leaf.bytes().start_bytes(),
                                leaf.access(),
                            ),
                            MovePathState::Moved,
                        )?;
                    }
                }
            }
            if let Err(error) = self
                .state
                .introduce_allocation_instance(allocation_id, allocation)
            {
                self.instance_failure(error)?;
                self.define(
                    pointer_result,
                    AbstractValue::Pointer(unknown_pointer().with_memory_access(Some(element))),
                )?;
                return self.define(permission_result, unknown_value(VirType::Permission));
            }
            let range =
                ByteRange::new(0, size_bytes).map_err(|_| TransferError::InvalidDerivedRange)?;
            let alignment = GuaranteedAlignment::new(alignment)
                .map_err(|_| TransferError::InvalidValidatedAlignment(alignment))?;
            self.define(
                pointer_result,
                AbstractValue::Pointer(
                    AbstractPointer::new(
                        AbstractProvenance::Known(allocation_id),
                        U64Interval::exact(0),
                        alignment,
                    )
                    .with_memory_access(Some(element)),
                ),
            )?;
            self.define(
                permission_result,
                AbstractValue::Permission(AbstractPermission::new(
                    AbstractProvenance::Known(allocation_id),
                    AbstractByteRange::Exact(range),
                    AccessPermission::Write,
                    FreeCapability::Yes,
                )),
            )
        } else {
            self.define(
                pointer_result,
                AbstractValue::Pointer(unknown_pointer().with_memory_access(Some(element))),
            )?;
            self.define(permission_result, unknown_value(VirType::Permission))
        }
    }

    fn local_storage(
        &mut self,
        pointer_result: VirValue,
        permission_result: VirValue,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let shape = self
            .memory
            .object_shape(access)
            .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
        let size_bytes = shape.size_bytes();
        let alignment_bytes = shape.alignment();
        let allocation_id = AbstractAllocationId::vir_local_storage_site(pointer_result.id);
        let mut allocation = AbstractAllocation::new_local(size_bytes, alignment_bytes)?;
        prepare_repeated_object_state(&mut allocation, &shape)?;
        allocation.seed_initialization_prefixes(self.memory, &shape);
        // Fresh variant-free storage has no payload. Keep this distinct from
        // Unknown so loop joins with a retired construction epoch stay empty.
        if shape.supports_resource_storage_reset() {
            for leaf in shape.resource_leaves() {
                let _ = allocation.set_resource_payload(
                    ResourcePayloadKey::new(leaf.bytes().start_bytes(), leaf.access()),
                    MovePathState::Moved,
                )?;
            }
        }
        if let Err(error) = self
            .state
            .introduce_allocation_instance(allocation_id, allocation)
        {
            self.instance_failure(error)?;
            self.define(
                pointer_result,
                AbstractValue::Pointer(unknown_pointer().with_memory_access(Some(access))),
            )?;
            return self.define(permission_result, unknown_value(VirType::Permission));
        }
        let range =
            ByteRange::new(0, size_bytes).map_err(|_| TransferError::InvalidDerivedRange)?;
        let alignment = GuaranteedAlignment::new(alignment_bytes)
            .map_err(|_| TransferError::InvalidValidatedAlignment(alignment_bytes))?;
        self.define(
            pointer_result,
            AbstractValue::Pointer(
                AbstractPointer::new(
                    AbstractProvenance::Known(allocation_id),
                    U64Interval::exact(0),
                    alignment,
                )
                .with_memory_access(Some(access)),
            ),
        )?;
        self.define(
            permission_result,
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(range),
                AccessPermission::Write,
                FreeCapability::No,
            )),
        )
    }

    fn index_address(
        &mut self,
        result: VirValue,
        base: VirValueId,
        index_id: VirValueId,
        access: AddressAccess,
        stride_bytes: u64,
        length: u64,
    ) -> Result<(), TransferError> {
        let index = word_fact(&self.state, index_id)?;
        let bounds = self.compare_words(
            RelationComparison::LessThan,
            word(index_id),
            RelationTerm::Constant(length),
        );
        self.require(
            ResourceObligationKind::IndexWithinBounds {
                index: index_id,
                values: index,
                length,
            },
            bounds,
        );
        let (delta, multiplication) = scale_pointer_interval(index, stride_bytes);
        self.require(
            ResourceObligationKind::IndexStrideNoOverflow {
                index: index_id,
                values: index,
                stride_bytes,
            },
            multiplication,
        );
        let expression = word_expression(&self.state, index_id, index)
            .and_then(|expression| expression.checked_scale(stride_bytes));
        let object_offsets = pointer_fact(&self.state, base)?
            .object_offsets()
            .offset_by_index(index, stride_bytes);
        self.typed_address(result, base, access, delta, expression)?;
        let source = pointer_fact(&self.state, base)?;
        self.set_pointer_paths(result.id, source.paths().element())?;
        let bytes = length
            .checked_mul(stride_bytes)
            .ok_or(TransferError::InvalidDerivedRange)?;
        self.set_pointer_domain(
            result.id,
            VirPointerDomain::Restricted(pointer_range(source, bytes)),
        )?;
        self.set_pointer_object_offsets(result.id, object_offsets, access.result)
    }

    fn slice_index_address(
        &mut self,
        result: VirValue,
        base: VirValueId,
        index_id: VirValueId,
        length_id: VirValueId,
        element: VirMemoryAccess,
        stride_bytes: u64,
    ) -> Result<(), TransferError> {
        let index = word_fact(&self.state, index_id)?;
        let length = word_fact(&self.state, length_id)?;
        let bounds = self.compare_words(
            RelationComparison::LessThan,
            word(index_id),
            word(length_id),
        );
        self.require(
            ResourceObligationKind::SliceIndexWithinBounds {
                index: index_id,
                values: index,
                length: length_id,
                length_values: length,
            },
            bounds,
        );
        let (delta, multiplication) = scale_pointer_interval(index, stride_bytes);
        self.require(
            ResourceObligationKind::IndexStrideNoOverflow {
                index: index_id,
                values: index,
                stride_bytes,
            },
            multiplication,
        );
        let expression = word_expression(&self.state, index_id, index)
            .and_then(|expression| expression.checked_scale(stride_bytes));
        let object_offsets = pointer_fact(&self.state, base)?
            .object_offsets()
            .offset_by_index(index, stride_bytes);
        self.typed_address(
            result,
            base,
            AddressAccess {
                source: element,
                result: element,
            },
            delta,
            expression,
        )?;
        let source = pointer_fact(&self.state, base)?;
        self.set_pointer_domain(result.id, source.domain())?;
        self.set_pointer_paths(result.id, source.paths())?;
        self.set_pointer_object_offsets(result.id, object_offsets, element)
    }

    #[allow(clippy::too_many_arguments)]
    fn slice_address(
        &mut self,
        pointer_result: VirValue,
        length_result: VirValue,
        base_id: VirValueId,
        start_id: VirValueId,
        end_id: VirValueId,
        source: VirMemoryAccess,
        slice: VirMemoryAccess,
        element: VirMemoryAccess,
        stride_bytes: u64,
        bounds: VirIndexBounds,
    ) -> Result<SliceAddressFacts, TransferError> {
        let start = word_fact(&self.state, start_id)?;
        let end = word_fact(&self.state, end_id)?;
        let length = match bounds {
            VirIndexBounds::Array { length } => U64Interval::exact(length),
            VirIndexBounds::Slice { length } => word_fact(&self.state, length)?,
        };
        self.require(
            ResourceObligationKind::SliceRangeOrdered {
                start: start_id,
                start_values: start,
                end: end_id,
                end_values: end,
            },
            self.compare_words(
                RelationComparison::LessOrEqual,
                word(start_id),
                word(end_id),
            ),
        );
        self.require(
            ResourceObligationKind::SliceRangeWithinBounds {
                end: end_id,
                end_values: end,
                length_values: length,
            },
            self.compare_words(
                RelationComparison::LessOrEqual,
                word(end_id),
                match bounds {
                    VirIndexBounds::Array { length } => RelationTerm::Constant(length),
                    VirIndexBounds::Slice { length } => word(length),
                },
            ),
        );

        let (start_delta, start_scale) = scale_pointer_interval(start, stride_bytes);
        let (end_delta, end_scale) = scale_pointer_interval(end, stride_bytes);
        let (source_delta, source_scale) = scale_pointer_interval(length, stride_bytes);
        self.require(
            ResourceObligationKind::SliceRangeStrideNoOverflow {
                length_values: length,
                stride_bytes,
            },
            source_scale,
        );
        self.require(
            ResourceObligationKind::IndexStrideNoOverflow {
                index: start_id,
                values: start,
                stride_bytes,
            },
            start_scale,
        );
        self.require(
            ResourceObligationKind::IndexStrideNoOverflow {
                index: end_id,
                values: end,
                stride_bytes,
            },
            end_scale,
        );

        let base = pointer_fact(&self.state, base_id)?;
        let expected_base_access = match bounds {
            VirIndexBounds::Array { .. } => source,
            VirIndexBounds::Slice { .. } => element,
        };
        self.require(
            ResourceObligationKind::PointerProvenanceKnown { pointer: base_id },
            known_provenance_status(base.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerMemoryAccessMatches {
                pointer: base_id,
                expected: expected_base_access,
                found: base.memory_access(),
            },
            memory_access_status(base.memory_access(), expected_base_access),
        );

        let (start_offset, start_add) = add_pointer_intervals(base.offset_bytes(), start_delta);
        let (end_offset, end_add) = add_pointer_intervals(base.offset_bytes(), end_delta);
        let (source_end, source_add) = add_pointer_intervals(base.offset_bytes(), source_delta);
        for (delta, status) in [
            (start_delta, start_add),
            (end_delta, end_add),
            (source_delta, source_add),
        ] {
            self.require(
                ResourceObligationKind::AddressCalculationNoOverflow {
                    base: base_id,
                    delta,
                },
                status,
            );
        }

        let base_expression = base.offset_expression().or_else(|| {
            base.offset_bytes()
                .exact_value()
                .map(AffineExpression::constant)
        });
        let scaled_expression = |id, interval| {
            word_expression(&self.state, id, interval)
                .and_then(|expression| expression.checked_scale(stride_bytes))
        };
        let start_expression = base_expression
            .zip(scaled_expression(start_id, start))
            .and_then(|(base, delta)| base.checked_add(delta));
        let end_expression = base_expression
            .zip(scaled_expression(end_id, end))
            .and_then(|(base, delta)| base.checked_add(delta));
        let source_end_expression = match bounds {
            VirIndexBounds::Array { length } => base_expression.and_then(|base| {
                length
                    .checked_mul(stride_bytes)
                    .and_then(|delta| base.checked_add_constant(delta))
            }),
            VirIndexBounds::Slice { length: length_id } => base_expression
                .zip(scaled_expression(length_id, length))
                .and_then(|(base, delta)| base.checked_add(delta)),
        };
        let selected_range =
            abstract_range_from_offsets(start_offset, start_expression, end_offset, end_expression);
        let source_range = abstract_range_from_offsets(
            base.offset_bytes(),
            base_expression,
            source_end,
            source_end_expression,
        );
        self.require_domain_range(base_id, base, source_range);

        let allocation_id = match base.provenance() {
            AbstractProvenance::Known(id) => Some(id),
            AbstractProvenance::Unknown => None,
        };
        let allocation = allocation_id.and_then(|id| self.state.allocation(id).cloned());
        if let Some(id) = allocation_id {
            self.require(
                ResourceObligationKind::AllocationTracked { allocation: id },
                if allocation.is_some() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
        }
        if let (Some(id), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AllocationLive { allocation: id },
                liveness_status(allocation.liveness()),
            );
            self.require(
                ResourceObligationKind::AccessWithinBounds {
                    allocation: id,
                    access: exact_abstract_range(source_range),
                    size_bytes: allocation.size_bytes(),
                },
                interval_le_status(source_end, U64Interval::exact(allocation.size_bytes())),
            );
        }

        let mutable = matches!(
            self.memory.kind(slice.ty),
            Some(VirMemoryTypeKind::Slice {
                mutability: VirMutability::Mutable,
                ..
            })
        );
        let start_alignment = start_expression.map_or_else(
            || offset_alignment(base.alignment(), start_delta),
            AffineExpression::guaranteed_alignment,
        );
        let derived = AbstractPointer::new(
            base.provenance(),
            start_offset,
            base.alignment().join(start_alignment),
        )
        .with_offset_expression(start_expression)
        .with_memory_access(Some(element))
        .with_domain(VirPointerDomain::Restricted(selected_range))
        .with_paths(match bounds {
            VirIndexBounds::Array { .. } => base.paths().element(),
            VirIndexBounds::Slice { .. } => base.paths().selected(),
        })
        .with_slice_footprint(
            ByteRange::new(start_offset.lower(), end_offset.upper())
                .ok()
                .map(|envelope| MemoryFootprint {
                    provenance: base.provenance(),
                    access: element,
                    stride_bytes,
                    range: selected_range,
                    envelope,
                }),
        )
        .with_object_offsets(base.object_offsets().offset_by_index(start, stride_bytes));
        let (_, element_alignment) = self.access_shape(element)?;
        if let (Some(_), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AddressObjectAligned {
                    pointer: pointer_result.id,
                    required_alignment: element_alignment,
                },
                object_alignment_status(derived, allocation, element_alignment),
            );
        }

        let exact_difference = word_expression(&self.state, start_id, start)
            .zip(word_expression(&self.state, end_id, end))
            .filter(|(a, b)| a.same_terms(*b))
            .and_then(|(a, b)| b.addend().checked_sub(a.addend()));
        let mut result_length =
            exact_difference.map_or_else(|| subtract_intervals(end, start), U64Interval::exact);
        if result_length.lower() == 0
            && result_length.upper() > 0
            && self
                .compare_words(RelationComparison::LessThan, word(start_id), word(end_id))
                .is_proven()
        {
            result_length = U64Interval::new(1, result_length.upper()).expect("nonempty range");
        }
        self.define(pointer_result, AbstractValue::Pointer(derived))?;
        self.define(length_result, AbstractValue::U64(result_length))?;
        if start.exact_value() == Some(0)
            && let Some(expression) = word_expression(&self.state, end_id, end)
        {
            self.state.set_word_expression(length_result.id, expression);
        }
        Ok(SliceAddressFacts {
            allocation_id,
            source_range,
            selected_range,
            mutable,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn slice_range(
        &mut self,
        pointer_result: VirValue,
        length_result: VirValue,
        permission_result: VirValue,
        base_id: VirValueId,
        permission_id: VirValueId,
        start_id: VirValueId,
        end_id: VirValueId,
        source: VirMemoryAccess,
        slice: VirMemoryAccess,
        element: VirMemoryAccess,
        stride_bytes: u64,
        bounds: VirIndexBounds,
    ) -> Result<(), TransferError> {
        let facts = self.slice_address(
            pointer_result,
            length_result,
            base_id,
            start_id,
            end_id,
            source,
            slice,
            element,
            stride_bytes,
            bounds,
        )?;
        let permission = permission_fact(&self.state, permission_id)?;
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: permission_id,
            },
            permission_availability_status(permission.availability()),
        );
        if let Some(id) = facts.allocation_id {
            self.require(
                ResourceObligationKind::PermissionMatchesAllocation {
                    permission: permission_id,
                    allocation: id,
                },
                provenance_match_status(permission.provenance(), id),
            );
        }
        self.require(
            ResourceObligationKind::PermissionCoversAccess {
                permission: permission_id,
                access: exact_abstract_range(facts.source_range),
            },
            self.range_contains(permission.range(), facts.source_range),
        );
        if facts.mutable {
            self.require(
                ResourceObligationKind::PermissionWritable {
                    permission: permission_id,
                },
                permission_writable_status(permission.access()),
            );
        }
        let result_access = if facts.mutable {
            match permission.access() {
                AccessPermission::Write => AccessPermission::Write,
                AccessPermission::Read | AccessPermission::MaybeWrite => {
                    AccessPermission::MaybeWrite
                }
            }
        } else {
            AccessPermission::Read
        };
        mark_permission_consumed(&mut self.state, permission_id)?;
        self.move_loan_authority(permission.authority(), permission_id, permission_result.id);
        self.define(
            permission_result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    permission.provenance(),
                    facts.selected_range,
                    result_access,
                    FreeCapability::No,
                )
                .with_authority(permission.authority()),
            ),
        )
    }

    fn typed_address(
        &mut self,
        result: VirValue,
        base_id: VirValueId,
        access: AddressAccess,
        delta: U64Interval,
        delta_expression: Option<AffineExpression>,
    ) -> Result<(), TransferError> {
        let (source_bytes, source_alignment) = self.access_shape(access.source)?;
        let (result_bytes, result_alignment) = self.access_shape(access.result)?;
        let base = pointer_fact(&self.state, base_id)?;
        self.require_domain_access(base_id, base, source_bytes);
        self.require(
            ResourceObligationKind::PointerProvenanceKnown { pointer: base_id },
            known_provenance_status(base.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerMemoryAccessMatches {
                pointer: base_id,
                expected: access.source,
                found: base.memory_access(),
            },
            memory_access_status(base.memory_access(), access.source),
        );

        let allocation_id = match base.provenance() {
            AbstractProvenance::Known(id) => Some(id),
            AbstractProvenance::Unknown => None,
        };
        let allocation = allocation_id.and_then(|id| self.state.allocation(id).cloned());
        if let Some(id) = allocation_id {
            self.require(
                ResourceObligationKind::AllocationTracked { allocation: id },
                if allocation.is_some() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
        }
        if let (Some(id), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AllocationLive { allocation: id },
                liveness_status(allocation.liveness()),
            );
            self.require(
                ResourceObligationKind::AddressObjectWithinBounds {
                    allocation: id,
                    offset: base.offset_bytes(),
                    object_bytes: source_bytes,
                    size_bytes: allocation.size_bytes(),
                },
                object_bounds_status(base.offset_bytes(), source_bytes, allocation.size_bytes()),
            );
            self.require(
                ResourceObligationKind::AddressObjectAligned {
                    pointer: base_id,
                    required_alignment: source_alignment,
                },
                object_alignment_status(base, allocation, source_alignment),
            );
        }

        let (offset, overflow) = add_pointer_intervals(base.offset_bytes(), delta);
        self.require(
            ResourceObligationKind::AddressCalculationNoOverflow {
                base: base_id,
                delta,
            },
            overflow,
        );
        let base_expression = base.offset_expression().or_else(|| {
            base.offset_bytes()
                .exact_value()
                .map(AffineExpression::constant)
        });
        let offset_expression = base_expression
            .zip(delta_expression)
            .and_then(|(base, delta)| base.checked_add(delta));
        let delta_alignment = delta_expression.map_or_else(
            || offset_alignment(base.alignment(), delta),
            AffineExpression::guaranteed_alignment,
        );
        let derived = AbstractPointer::new(
            base.provenance(),
            offset,
            base.alignment().join(delta_alignment),
        )
        .with_offset_expression(offset_expression)
        .with_memory_access(Some(access.result))
        .with_paths(crate::VirPointerPaths::default())
        .with_object_offsets(
            delta
                .exact_value()
                .map_or(AbstractObjectOffsets::Unknown, |delta| {
                    base.object_offsets().offset_by_exact(delta)
                }),
        );

        self.require_domain_range(base_id, base, pointer_range(derived, result_bytes));
        let derived = derived.with_domain(VirPointerDomain::Restricted(pointer_range(
            derived,
            result_bytes,
        )));

        if let (Some(id), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AddressObjectWithinBounds {
                    allocation: id,
                    offset,
                    object_bytes: result_bytes,
                    size_bytes: allocation.size_bytes(),
                },
                object_bounds_status(offset, result_bytes, allocation.size_bytes()),
            );
            self.require(
                ResourceObligationKind::AddressObjectAligned {
                    pointer: result.id,
                    required_alignment: result_alignment,
                },
                object_alignment_status(derived, allocation, result_alignment),
            );
        }
        self.define(result, AbstractValue::Pointer(derived))
    }

    fn access_shape(&self, access: VirMemoryAccess) -> Result<(u64, u64), TransferError> {
        self.memory
            .layout(access.layout)
            .filter(|layout| layout.ty == access.ty)
            .map(|layout| (layout.size_bytes, layout.alignment))
            .ok_or(TransferError::InvalidValidatedMemoryAccess(access))
    }

    fn pointer_offset(
        &mut self,
        result: VirValue,
        base_id: VirValueId,
        delta_id: VirValueId,
    ) -> Result<(), TransferError> {
        let base = pointer_fact(&self.state, base_id)?;
        let delta = word_fact(&self.state, delta_id)?;
        self.require_domain_access(base_id, base, 0);
        let delta_expression = word_expression(&self.state, delta_id, delta);
        self.require(
            ResourceObligationKind::PointerProvenanceKnown { pointer: base_id },
            known_provenance_status(base.provenance()),
        );

        let (offset, overflow_status) = add_pointer_intervals(base.offset_bytes(), delta);
        self.require(
            ResourceObligationKind::PointerOffsetNoOverflow {
                base: base_id,
                delta,
            },
            overflow_status,
        );

        if let AbstractProvenance::Known(allocation_id) = base.provenance() {
            let allocation = self.state.allocation(allocation_id).cloned();
            self.require(
                ResourceObligationKind::AllocationTracked {
                    allocation: allocation_id,
                },
                if allocation.is_some() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
            if let Some(allocation) = allocation {
                self.require(
                    ResourceObligationKind::AllocationLive {
                        allocation: allocation_id,
                    },
                    liveness_status(allocation.liveness()),
                );
                let bounds = if offset.upper() <= allocation.size_bytes() {
                    ObligationStatus::Proven
                } else if offset.lower() > allocation.size_bytes() {
                    ObligationStatus::Refuted
                } else {
                    ObligationStatus::Unknown
                };
                self.require(
                    ResourceObligationKind::PointerOffsetWithinBounds {
                        allocation: allocation_id,
                        offset,
                        size_bytes: allocation.size_bytes(),
                    },
                    bounds,
                );
            }
        }

        let base_expression = base.offset_expression().or_else(|| {
            base.offset_bytes()
                .exact_value()
                .map(AffineExpression::constant)
        });
        let offset_expression = base_expression
            .zip(delta_expression)
            .and_then(|(base, delta)| base.checked_add(delta));
        let delta_alignment = delta_expression.map_or_else(
            || offset_alignment(base.alignment(), delta),
            AffineExpression::guaranteed_alignment,
        );
        let selection =
            abstract_range_from_offsets(offset, offset_expression, offset, offset_expression);
        self.require_domain_range(base_id, base, selection);
        self.define(
            result,
            AbstractValue::Pointer(
                AbstractPointer::new(
                    base.provenance(),
                    offset,
                    base.alignment().join(delta_alignment),
                )
                .with_offset_expression(offset_expression)
                .with_memory_access(base.memory_access())
                .with_paths(base.paths())
                .with_domain(base.domain())
                .with_slice_footprint(base.slice_footprint())
                .with_object_offsets(
                    delta
                        .exact_value()
                        .map_or(AbstractObjectOffsets::Unknown, |delta| {
                            base.object_offsets().offset_by_exact(delta)
                        }),
                ),
            ),
        )
    }

    fn memory_access(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        required_access: AccessPermission,
        initialization: InitializationRequirement,
        effect: MemoryEffect,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let first_obligation = self.obligations.len();
        let (access_bytes, required_alignment) = self.access_shape(access)?;
        let pointer = pointer_fact(&self.state, pointer_id)?;
        let permission = permission_fact(&self.state, permission_id)?;
        self.require_domain_access(pointer_id, pointer, access_bytes);
        self.require(
            ResourceObligationKind::PointerProvenanceKnown {
                pointer: pointer_id,
            },
            known_provenance_status(pointer.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerMemoryAccessMatches {
                pointer: pointer_id,
                expected: access,
                found: pointer.memory_access(),
            },
            memory_access_status(pointer.memory_access(), access),
        );

        let envelope = access_envelope(pointer.offset_bytes(), access_bytes);
        let allocation_id = match pointer.provenance() {
            AbstractProvenance::Known(id) => Some(id),
            AbstractProvenance::Unknown => None,
        };
        let allocation = allocation_id.and_then(|id| self.state.allocation(id).cloned());

        if let Some(id) = allocation_id {
            self.require(
                ResourceObligationKind::AllocationTracked { allocation: id },
                if allocation.is_some() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
        }

        if let (Some(id), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AllocationLive { allocation: id },
                liveness_status(allocation.liveness()),
            );
            self.require(
                ResourceObligationKind::AccessWithinBounds {
                    allocation: id,
                    access: envelope,
                    size_bytes: allocation.size_bytes(),
                },
                object_bounds_status(
                    pointer.offset_bytes(),
                    access_bytes,
                    allocation.size_bytes(),
                ),
            );
            self.require(
                ResourceObligationKind::AccessAligned {
                    pointer: pointer_id,
                    required_alignment,
                },
                object_alignment_status(pointer, allocation, required_alignment),
            );

            let mut status = envelope.map_or(ObligationStatus::Unknown, |range| {
                initialization_status(allocation.initialization().classify(range), initialization)
            });
            if matches!(initialization, InitializationRequirement::Initialized)
                && !status.is_proven()
                && self.state.initialized_prefix_covers(
                    id,
                    access,
                    super::relation::range::access_range(pointer, access_bytes),
                    self.relation_limits,
                    &self.relations.queries,
                )
            {
                status = ObligationStatus::Proven;
            }
            match initialization {
                InitializationRequirement::None => {}
                InitializationRequirement::Initialized => self.require(
                    ResourceObligationKind::MemoryInitialized {
                        allocation: id,
                        access: envelope,
                    },
                    status,
                ),
                InitializationRequirement::Uninitialized => self.require(
                    ResourceObligationKind::MemoryUninitialized {
                        allocation: id,
                        access: envelope,
                    },
                    status,
                ),
            }
            self.active_variant_access_obligations(
                pointer_id,
                pointer,
                allocation,
                access,
                access_bytes,
            )?;
        }

        self.permission_access_obligations(
            permission_id,
            permission,
            PermissionAccessContext {
                allocation: allocation_id,
                envelope,
                pointer,
                required_access,
                access_bytes,
            },
        );

        if matches!(effect, MemoryEffect::WriteValue) {
            if let (Some(id), Some(possible)) = (allocation_id, envelope)
                && let Some(allocation) = self.state.allocation_mut(id)
                && possible.end() <= allocation.size_bytes()
            {
                allocation.forget_uninitialized(possible)?;
                if let Some(definite) = definite_write_range(pointer.offset_bytes(), access_bytes) {
                    allocation.mark_initialized(definite)?;
                    allocation.mark_valid(definite)?;
                }
            }
            if let Some(before) = allocation.as_ref()
                && self.obligations[first_obligation..]
                    .iter()
                    .all(|obligation| obligation.status().is_proven())
            {
                self.state
                    .advance_initialization_prefixes(before, pointer, access);
            }
        }
        Ok(())
    }

    fn active_variant_access_obligations(
        &mut self,
        pointer_id: VirValueId,
        pointer: AbstractPointer,
        allocation: &AbstractAllocation,
        access: VirMemoryAccess,
        access_bytes: u64,
    ) -> Result<(), TransferError> {
        let target = access_envelope(pointer.offset_bytes(), access_bytes);
        if !allocation.object_state().is_precise()
            && let AbstractProvenance::Known(allocation_id) = pointer.provenance()
        {
            self.require(
                ResourceObligationKind::ObjectStateWithinBudget {
                    allocation: allocation_id,
                },
                ObligationStatus::Unknown,
            );
        }
        for (key, active) in allocation.object_state().active_variants() {
            let shape = self
                .memory
                .object_shape(key.access())
                .map_err(|_| TransferError::InvalidValidatedMemoryAccess(key.access()))?;
            let mut allowed = BTreeSet::new();
            let mut related = false;
            for variant in shape
                .variants()
                .iter()
                .filter(|variant| variant.path().segments().is_empty())
            {
                for leaf in variant
                    .leaves()
                    .iter()
                    .filter(|leaf| leaf.access() == access)
                {
                    let Some(start) = key.offset_bytes().checked_add(leaf.bytes().start_bytes())
                    else {
                        continue;
                    };
                    let Some(end) = key.offset_bytes().checked_add(leaf.bytes().end_bytes()) else {
                        continue;
                    };
                    let leaf_range = ByteRange::new(start, end)
                        .map_err(|_| TransferError::InvalidDerivedRange)?;
                    if target.is_some_and(|target| target.overlaps(leaf_range)) {
                        related = true;
                    }
                    if pointer.offset_bytes().exact_value().is_some_and(|offset| {
                        offset == leaf_range.start() && access_bytes == leaf_range.length()
                    }) {
                        allowed.insert(variant.variant());
                    }
                }
            }
            if !related {
                continue;
            }
            let status = if pointer.offset_bytes().exact_value().is_none() || allowed.is_empty() {
                ObligationStatus::Unknown
            } else {
                active_variant_allows_access(active, &allowed)
            };
            self.require(
                ResourceObligationKind::ActiveVariantAllowsAccess {
                    pointer: pointer_id,
                    enum_access: key.access(),
                    enum_offset_bytes: key.offset_bytes(),
                },
                status,
            );
        }
        Ok(())
    }

    fn resource_initialize(
        &mut self,
        destination_id: VirValueId,
        destination_permission_id: VirValueId,
        value_id: VirValueId,
        value_permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let resource = storable_resource(self.memory, access)?;
        let pointee_access = resource.pointee();
        let destination = pointer_fact(&self.state, destination_id)?;
        let value = pointer_fact(&self.state, value_id)?;
        let value_permission = permission_fact(&self.state, value_permission_id)?;

        self.require(
            ResourceObligationKind::PointerMemoryAccessMatches {
                pointer: value_id,
                expected: pointee_access,
                found: value.memory_access(),
            },
            memory_access_status(value.memory_access(), pointee_access),
        );
        let reference_status = match resource {
            StorableResource::Own { .. } => {
                self.require_owner_payload_obligations(
                    value_id,
                    value_permission_id,
                    value,
                    value_permission,
                );
                None
            }
            StorableResource::Reference { kind, .. } => {
                let (loan, status) = permission_loan_access_status(
                    &self.state,
                    value_permission_id,
                    value_permission,
                    LoanAccess::bytes(
                        value,
                        self.memory
                            .object_shape(pointee_access)
                            .map_err(|_| TransferError::InvalidDerivedRange)?
                            .size_bytes(),
                        loan_access(kind),
                    ),
                    self.relation_limits,
                    &self.relations,
                );
                self.require(
                    ResourceObligationKind::LoanCompatible {
                        loan,
                        permission: value_permission_id,
                        access: pointer_access_range(self.memory, value, pointee_access),
                        required: loan_access(kind),
                    },
                    status,
                );
                Some((loan, status))
            }
        };
        self.memory_access(
            destination_id,
            destination_permission_id,
            AccessPermission::Write,
            InitializationRequirement::Uninitialized,
            MemoryEffect::WriteValue,
            access,
        )?;

        let destination_offset = destination.offset_bytes().exact_value();
        self.require(
            ResourceObligationKind::ResourcePayloadLocationExact {
                pointer: destination_id,
                access,
            },
            if destination_offset.is_some() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        );
        if let (AbstractProvenance::Known(allocation_id), Some(offset)) =
            (destination.provenance(), destination_offset)
        {
            let key = ResourcePayloadKey::new(offset, access);
            let exact_reference =
                reference_status.is_none_or(|(loan, status)| loan.is_some() && status.is_proven());
            let permission = value_permission
                .with_availability(PermissionAvailability::Available)
                .with_authority(if exact_reference {
                    value_permission.authority()
                } else {
                    PermissionAuthority::Unknown
                });
            if let Some(allocation) = self.state.allocation_mut(allocation_id) {
                let _ = allocation.set_resource_payload(
                    key,
                    MovePathState::available(TypedResourcePayload::new(value, permission)),
                )?;
            }
            if let Some((Some(loan_id), status)) = reference_status
                && let Some(loan) = self.state.loan_mut(loan_id)
            {
                if status.is_proven()
                    && loan.move_authority_to_storage(value_permission_id, allocation_id, key)
                {
                    // The authority now lives in the typed object payload.
                } else {
                    loan.set_activity(LoanActivity::MaybeActive);
                }
            }
        }
        mark_permission_consumed(&mut self.state, value_permission_id)
    }

    fn resource_take(
        &mut self,
        pointer_result: VirValue,
        permission_result: VirValue,
        source_id: VirValueId,
        source_permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let resource = storable_resource(self.memory, access)?;
        let pointee_access = resource.pointee();
        let source = pointer_fact(&self.state, source_id)?;
        self.memory_access(
            source_id,
            source_permission_id,
            AccessPermission::Write,
            InitializationRequirement::Initialized,
            MemoryEffect::None,
            access,
        )?;

        let allocation_id = match source.provenance() {
            AbstractProvenance::Known(allocation) => Some(allocation),
            AbstractProvenance::Unknown => None,
        };
        let offset = source.offset_bytes().exact_value();
        self.require(
            ResourceObligationKind::ResourcePayloadLocationExact {
                pointer: source_id,
                access,
            },
            if offset.is_some() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        );
        let payload_state = allocation_id
            .zip(offset)
            .and_then(|(allocation, offset)| {
                self.state.allocation(allocation).map(|allocation| {
                    allocation.resource_payload(ResourcePayloadKey::new(offset, access))
                })
            })
            .unwrap_or(MovePathState::Unknown);
        self.require(
            ResourceObligationKind::ResourcePayloadAvailable {
                allocation: allocation_id,
                offset_bytes: offset,
                access,
            },
            move_path_availability_status(&payload_state),
        );

        let (pointer, mut permission) = match payload_state {
            MovePathState::Available(payload) => (payload.pointer(), payload.permission()),
            MovePathState::Moved | MovePathState::Unknown => (
                unknown_pointer().with_memory_access(Some(pointee_access)),
                fresh_unknown_permission(),
            ),
        };
        let key = offset.map(|offset| ResourcePayloadKey::new(offset, access));
        if let StorableResource::Reference { kind, .. } = resource {
            let (loan_id, status) = match (allocation_id, key, permission.authority()) {
                (Some(allocation), Some(key), PermissionAuthority::Loan(loan_id)) => {
                    let status =
                        self.state
                            .loan(loan_id)
                            .map_or(ObligationStatus::Unknown, |loan| {
                                combine_statuses([
                                    stored_loan_authority_status(
                                        loan, allocation, key, loan_id, kind,
                                    ),
                                    loan_activity_access_status(loan.activity()),
                                    loan_authority_access_status_for_payload(
                                        loan,
                                        pointer,
                                        self.memory
                                            .layout(pointee_access.layout)
                                            .map(|layout| layout.size_bytes),
                                        loan_access(kind),
                                    ),
                                ])
                            });
                    (Some(loan_id), status)
                }
                (_, _, PermissionAuthority::Owner | PermissionAuthority::Loan(_)) => {
                    (None, ObligationStatus::Refuted)
                }
                (_, _, PermissionAuthority::Unknown) => (None, ObligationStatus::Unknown),
            };
            self.require(
                ResourceObligationKind::LoanCompatible {
                    loan: loan_id,
                    permission: permission_result.id,
                    access: pointer_access_range(self.memory, pointer, pointee_access),
                    required: loan_access(kind),
                },
                status,
            );
            if let (Some(loan_id), Some(allocation), Some(key)) = (loan_id, allocation_id, key)
                && let Some(loan) = self.state.loan_mut(loan_id)
            {
                if status.is_proven()
                    && loan.move_authority_from_storage(allocation, key, permission_result.id)
                {
                    permission = permission.with_authority(PermissionAuthority::Loan(loan_id));
                } else {
                    permission = permission.with_authority(PermissionAuthority::Unknown);
                    loan.set_activity(LoanActivity::MaybeActive);
                }
            } else {
                permission = permission.with_authority(PermissionAuthority::Unknown);
            }
        }
        self.define(pointer_result, AbstractValue::Pointer(pointer))?;
        self.define(permission_result, AbstractValue::Permission(permission))?;

        if let (Some(allocation_id), Some(offset)) = (allocation_id, offset)
            && let Some(allocation) = self.state.allocation_mut(allocation_id)
        {
            let width = self
                .memory
                .layout(access.layout)
                .ok_or(TransferError::InvalidValidatedMemoryAccess(access))?
                .size_bytes;
            let range = ByteRange::from_start_and_length(offset, width)
                .map_err(|_| TransferError::InvalidDerivedRange)?;
            allocation.mark_uninitialized(range)?;
            let _ = allocation.set_resource_payload(
                ResourcePayloadKey::new(offset, access),
                MovePathState::Moved,
            )?;
        }
        Ok(())
    }

    fn require_owner_payload_obligations(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        pointer: AbstractPointer,
        permission: AbstractPermission,
    ) {
        self.require(
            ResourceObligationKind::PointerProvenanceKnown {
                pointer: pointer_id,
            },
            known_provenance_status(pointer.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerAtAllocationBase {
                pointer: pointer_id,
            },
            base_pointer_status(pointer.offset_bytes()),
        );
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: permission_id,
            },
            permission_availability_status(permission.availability()),
        );
        self.require(
            ResourceObligationKind::PermissionCanFree {
                permission: permission_id,
            },
            free_capability_status(permission.free_capability()),
        );
        let full_access = match pointer.provenance() {
            AbstractProvenance::Known(allocation) => self
                .state
                .allocation(allocation)
                .and_then(|allocation| ByteRange::new(0, allocation.size_bytes()).ok()),
            AbstractProvenance::Unknown => None,
        };
        let (loan, loan_status) = permission_loan_access_status(
            &self.state,
            permission_id,
            permission,
            LoanAccess::whole(pointer, full_access, AccessPermission::Write),
            self.relation_limits,
            &self.relations,
        );
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan,
                permission: permission_id,
                access: full_access,
                required: AccessPermission::Write,
            },
            loan_status,
        );
        if let AbstractProvenance::Known(allocation_id) = pointer.provenance() {
            let allocation = self.state.allocation(allocation_id).cloned();
            self.require(
                ResourceObligationKind::AllocationTracked {
                    allocation: allocation_id,
                },
                if allocation.is_some() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
            self.require(
                ResourceObligationKind::PermissionMatchesAllocation {
                    permission: permission_id,
                    allocation: allocation_id,
                },
                provenance_match_status(permission.provenance(), allocation_id),
            );
            if let Some(allocation) = allocation {
                self.require(
                    ResourceObligationKind::AllocationLive {
                        allocation: allocation_id,
                    },
                    liveness_status(allocation.liveness()),
                );
                self.require(
                    ResourceObligationKind::AllocationOwned {
                        allocation: allocation_id,
                    },
                    ownership_status(allocation.ownership()),
                );
                self.require(
                    ResourceObligationKind::PermissionCoversAllocation {
                        permission: permission_id,
                        allocation: allocation_id,
                    },
                    full_permission_status(permission.range(), allocation.size_bytes()),
                );
            }
        }
    }

    fn object_transfer(&mut self, effect: ObjectTransferEffect) -> Result<(), TransferError> {
        let destination = self.object_access_facts(
            effect.destination,
            effect.destination_permission,
            effect.access,
            AccessPermission::Write,
        )?;
        let source = self.object_access_facts(
            effect.source,
            effect.source_permission,
            effect.access,
            if matches!(effect.source_mode, VirObjectSourceMode::Move) {
                AccessPermission::Write
            } else {
                AccessPermission::Read
            },
        )?;

        self.require(
            ResourceObligationKind::ObjectNonOverlapping {
                destination: effect.destination,
                source: effect.source,
                size_bytes: source.shape.size_bytes(),
            },
            self.relations.queries.non_overlapping(
                &self.state,
                destination.pointer,
                source.pointer,
                source.shape.size_bytes(),
                self.relation_limits,
            ),
        );
        match effect.source_mode {
            VirObjectSourceMode::Copy => self.require(
                ResourceObligationKind::ObjectTriviallyCopyable {
                    access: effect.access,
                },
                copyable_object_status(self.memory, effect.access),
            ),
            VirObjectSourceMode::Move => self.require(
                ResourceObligationKind::ObjectMoveSupported {
                    access: effect.access,
                },
                movable_object_status(self.memory, &source.shape),
            ),
        }

        let source_mask = active_object_mask(&source);
        self.require_active_variants(&source, &source_mask);
        self.require_object_initialization(
            &source,
            &source_mask.possible_value_bytes,
            InitializationRequirement::Initialized,
        );
        self.require_object_validity(&source, &source_mask.possible_value_bytes);
        self.require_object_resource_payloads(&source, &source_mask);

        let destination_mask = active_object_mask(&destination);
        match effect.destination_mode {
            VirObjectDestinationMode::Initialize => self.require_object_initialization(
                &destination,
                &source_mask.possible_value_bytes,
                InitializationRequirement::Uninitialized,
            ),
            VirObjectDestinationMode::Replace => {
                self.require_active_variants(&destination, &destination_mask);
                self.require_object_initialization(
                    &destination,
                    &destination_mask.possible_value_bytes,
                    InitializationRequirement::Initialized,
                );
                self.require_object_validity(&destination, &destination_mask.possible_value_bytes);
                self.require(
                    ResourceObligationKind::ObjectTriviallyDroppable {
                        access: effect.access,
                    },
                    droppable_object_status(self.memory, effect.access),
                );
            }
        }

        let overwritten_destination =
            if matches!(effect.destination_mode, VirObjectDestinationMode::Replace) {
                source_mask
                    .possible_value_bytes
                    .union(&destination_mask.possible_value_bytes)
            } else {
                source_mask.possible_value_bytes.clone()
            };
        let preserves_complete_value_state =
            matches!(effect.destination_mode, VirObjectDestinationMode::Replace)
                && source_mask.possible_value_bytes == source_mask.guaranteed_value_bytes
                && destination_mask.possible_value_bytes == destination_mask.guaranteed_value_bytes
                && source_mask.possible_value_bytes == destination_mask.possible_value_bytes;
        // A complete trivial replacement preserves initialization and validity
        // even when the destination offset is an interval: every possible
        // selected object was required to be valid before the operation and
        // receives a complete valid value. Forgetting the entire offset
        // envelope here would lose facts about unaffected array elements.
        if !preserves_complete_value_state {
            self.apply_object_write(
                &destination,
                &overwritten_destination,
                &source_mask.guaranteed_value_bytes,
            )?;
        }
        if matches!(effect.destination_mode, VirObjectDestinationMode::Replace)
            && destination_mask.guaranteed_value_bytes.is_precise()
            && source_mask.possible_value_bytes.is_precise()
        {
            let mut retired = destination_mask.guaranteed_value_bytes.clone();
            for range in source_mask.possible_value_bytes.ranges() {
                retired.remove(*range);
            }
            self.apply_object_uninitialized(&destination, &retired)?;
        }
        self.copy_active_variants(&source, &destination, &source_mask)?;
        // Representation cache invalidation must not forget independently
        // known empty payload slots (notably inactive enum variants).
        if let (Some(id), Some(previous)) = (destination.allocation_id, &destination.allocation)
            && let Some(allocation) = self.state.allocation_mut(id)
        {
            restore_empty_resource_paths(allocation, &empty_resource_paths(previous))?;
        }
        self.transfer_object_resource_payloads(
            &source,
            &destination,
            &source_mask,
            effect.source_mode,
        )?;
        if matches!(effect.source_mode, VirObjectSourceMode::Move) {
            self.apply_object_deinitialize(&source, &source_mask)?;
        }
        Ok(())
    }

    fn require_object_resource_payloads(
        &mut self,
        object: &ObjectAccessFacts,
        mask: &ActiveObjectMask,
    ) {
        let base = object.pointer.offset_bytes().exact_value();
        for leaf in &mask.possible_resource_leaves {
            let offset = base.and_then(|base| base.checked_add(leaf.bytes().start_bytes()));
            let state = object
                .allocation
                .as_ref()
                .zip(offset)
                .map(|(allocation, offset)| {
                    allocation.resource_payload(ResourcePayloadKey::new(offset, leaf.access()))
                })
                .unwrap_or(MovePathState::Unknown);
            let guaranteed = mask
                .guaranteed_resource_leaves
                .iter()
                .any(|candidate| candidate == leaf);
            let availability = if guaranteed {
                match (&state, leaf.kind()) {
                    (MovePathState::Available(payload), VirPointerKind::Reference) => {
                        let PermissionAuthority::Loan(loan_id) = payload.permission().authority()
                        else {
                            self.require(
                                ResourceObligationKind::ResourcePayloadAvailable {
                                    allocation: object.allocation_id,
                                    offset_bytes: offset,
                                    access: leaf.access(),
                                },
                                ObligationStatus::Refuted,
                            );
                            continue;
                        };
                        object.allocation_id.zip(offset).map_or(
                            ObligationStatus::Unknown,
                            |(allocation, offset)| {
                                let key = ResourcePayloadKey::new(offset, leaf.access());
                                self.state
                                    .loan(loan_id)
                                    .map_or(ObligationStatus::Unknown, |loan| {
                                        combine_statuses([
                                            stored_loan_authority_status(
                                                loan,
                                                allocation,
                                                key,
                                                loan_id,
                                                if leaf.mutability() == VirMutability::Const {
                                                    VirLoanKind::Shared
                                                } else {
                                                    VirLoanKind::Mutable
                                                },
                                            ),
                                            loan_activity_access_status(loan.activity()),
                                            loan_authority_access_status_for_payload(
                                                loan,
                                                payload.pointer(),
                                                reference_pointee(self.memory, leaf.access())
                                                    .ok()
                                                    .and_then(|pointee| {
                                                        self.memory
                                                            .layout(pointee.layout)
                                                            .map(|layout| layout.size_bytes)
                                                    }),
                                                if leaf.mutability() == VirMutability::Const {
                                                    AccessPermission::Read
                                                } else {
                                                    AccessPermission::Write
                                                },
                                            ),
                                        ])
                                    })
                            },
                        )
                    }
                    (MovePathState::Available(_), VirPointerKind::Own) => ObligationStatus::Proven,
                    (MovePathState::Available(_), VirPointerKind::Raw) => ObligationStatus::Refuted,
                    (MovePathState::Moved, _) => ObligationStatus::Refuted,
                    (MovePathState::Unknown, _) => ObligationStatus::Unknown,
                }
            } else {
                ObligationStatus::Unknown
            };
            self.require(
                ResourceObligationKind::ResourcePayloadAvailable {
                    allocation: object.allocation_id,
                    offset_bytes: offset,
                    access: leaf.access(),
                },
                availability,
            );
        }
    }

    fn transfer_object_resource_payloads(
        &mut self,
        source: &ObjectAccessFacts,
        destination: &ObjectAccessFacts,
        mask: &ActiveObjectMask,
        source_mode: VirObjectSourceMode,
    ) -> Result<(), TransferError> {
        let (Some(source_id), Some(source_base), Some(destination_id), Some(destination_base)) = (
            source.allocation_id,
            source.pointer.offset_bytes().exact_value(),
            destination.allocation_id,
            destination.pointer.offset_bytes().exact_value(),
        ) else {
            return Ok(());
        };
        let payloads = mask
            .guaranteed_resource_leaves
            .iter()
            .filter_map(|leaf| {
                let source_offset = source_base.checked_add(leaf.bytes().start_bytes())?;
                let state = self
                    .state
                    .allocation(source_id)?
                    .resource_payload(ResourcePayloadKey::new(source_offset, leaf.access()));
                let MovePathState::Available(payload) = state else {
                    return None;
                };
                let destination_offset =
                    destination_base.checked_add(leaf.bytes().start_bytes())?;
                Some((
                    leaf.clone(),
                    ResourcePayloadKey::new(source_offset, leaf.access()),
                    ResourcePayloadKey::new(destination_offset, leaf.access()),
                    payload,
                ))
            })
            .collect::<Vec<_>>();
        for (leaf, source_key, destination_key, payload) in &payloads {
            if leaf.kind() != VirPointerKind::Reference {
                continue;
            }
            let PermissionAuthority::Loan(loan_id) = payload.permission().authority() else {
                continue;
            };
            match source_mode {
                VirObjectSourceMode::Move => {
                    if let Some(loan) = self.state.loan_mut(loan_id)
                        && !loan.move_stored_authority(
                            source_id,
                            *source_key,
                            destination_id,
                            *destination_key,
                        )
                    {
                        loan.set_activity(LoanActivity::MaybeActive);
                    }
                }
                VirObjectSourceMode::Copy => {
                    let context = self
                        .loan_context
                        .ok_or(TransferError::MissingLoanTransferContext)?;
                    let alias_status = self.require_alias_budget(loan_id, context.limits);
                    if alias_status.is_proven()
                        && let Some(loan) = self.state.loan_mut(loan_id)
                    {
                        loan.add_stored_authority(destination_id, *destination_key);
                    } else if let Some(loan) = self.state.loan_mut(loan_id) {
                        loan.set_activity(LoanActivity::MaybeActive);
                    }
                }
            }
        }
        if let Some(allocation) = self.state.allocation_mut(destination_id) {
            for (_, _, key, payload) in payloads {
                let _ = allocation.set_resource_payload(key, MovePathState::Available(payload))?;
            }
        }
        Ok(())
    }

    fn resource_storage_reset(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Write)?;
        let mask = active_object_mask(&object);
        let mut resources = ByteSet::new();
        for leaf in &mask.possible_resource_leaves {
            resources.insert(object_relative_range(leaf.bytes())?);
        }
        self.require_object_initialization(
            &object,
            &resources,
            InitializationRequirement::Uninitialized,
        );
        let Some(allocation_id) = object.allocation_id else {
            return Ok(());
        };
        let status = object.allocation.as_ref().map_or(
            ObligationStatus::Unknown,
            allocation_resource_payload_empty_status,
        );
        self.require(
            ResourceObligationKind::AllocationResourcePayloadEmpty {
                allocation: allocation_id,
            },
            status,
        );
        if !status.is_proven() {
            return Ok(());
        }
        self.apply_object_deinitialize(&object, &mask)?;
        if let Some(base) = object.pointer.offset_bytes().exact_value()
            && let Some(allocation) = self.state.allocation_mut(allocation_id)
        {
            for leaf in object.shape.resource_leaves() {
                if let Some(end) = base.checked_add(leaf.bytes().end_bytes())
                    && end <= allocation.size_bytes()
                {
                    let key =
                        ResourcePayloadKey::new(base + leaf.bytes().start_bytes(), leaf.access());
                    let _ = allocation.set_resource_payload(key, MovePathState::Moved)?;
                }
            }
        }
        Ok(())
    }

    fn object_deinitialize(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Write)?;
        let mask = active_object_mask(&object);
        self.require_active_variants(&object, &mask);
        self.require_object_initialization(
            &object,
            &mask.possible_value_bytes,
            InitializationRequirement::Initialized,
        );
        self.require_object_validity(&object, &mask.possible_value_bytes);
        self.require(
            ResourceObligationKind::ObjectTriviallyDroppable { access },
            droppable_object_status(self.memory, access),
        );
        self.apply_object_deinitialize(&object, &mask)
    }

    fn object_drop(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
        condition_id: VirValueId,
    ) -> Result<(), TransferError> {
        match self.require_drop_flag(condition_id)? {
            Some(true) => {}
            Some(false) | None => return Ok(()),
        }
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Write)?;
        let mask = active_object_mask(&object);
        self.require(
            ResourceObligationKind::ObjectBuiltinDroppable { access },
            builtin_droppable_object_status(self.memory, access),
        );

        // Fresh or wholly moved tagged storage has no representation to decode.
        // Retirement is safe only with independently proven byte and payload
        // absence over the whole object; Unknown is never an empty value.
        if !mask.sites.is_empty()
            && let Some(empty_bytes) = empty_tagged_storage(&object, self.memory)
        {
            self.require_object_initialization(
                &object,
                &empty_bytes,
                InitializationRequirement::Uninitialized,
            );
            self.require(
                ResourceObligationKind::ObjectResourcePayloadEmpty {
                    allocation: object.allocation_id,
                    offset_bytes: object.pointer.offset_bytes().exact_value(),
                    access,
                },
                object_resource_payload_empty_status(&object, self.memory),
            );
            return Ok(());
        }
        self.require_active_variants(&object, &mask);

        // Cleanup observes representation tags and present resource payloads,
        // not trivial payload bytes. In particular, moving an aggregate field
        // out of an enum may retire those bytes without retiring the root tag.
        let mut tags = ByteSet::new();
        for (site, _, _) in &mask.sites {
            tags.insert(site.tag);
        }
        if !tags.is_empty() {
            self.require_object_initialization(
                &object,
                &tags,
                InitializationRequirement::Initialized,
            );
            self.require_object_validity(&object, &tags);
        }

        let base = object.pointer.offset_bytes().exact_value();
        let mut dropped = Vec::new();
        for leaf in &mask.possible_resource_leaves {
            let offset = base.and_then(|base| base.checked_add(leaf.bytes().start_bytes()));
            let state = object
                .allocation
                .as_ref()
                .zip(offset)
                .map(|(allocation, offset)| {
                    allocation.resource_payload(ResourcePayloadKey::new(offset, leaf.access()))
                })
                .unwrap_or(MovePathState::Unknown);
            let guaranteed = mask
                .guaranteed_resource_leaves
                .iter()
                .any(|candidate| candidate == leaf);
            let status = match state {
                MovePathState::Available(ref payload) if guaranteed => match leaf.kind() {
                    VirPointerKind::Own => object_drop_payload_status(&self.state, payload),
                    VirPointerKind::Reference => {
                        let PermissionAuthority::Loan(loan_id) = payload.permission().authority()
                        else {
                            self.require(
                                ResourceObligationKind::ObjectDropPayloadValid {
                                    allocation: object.allocation_id,
                                    offset_bytes: offset,
                                    access: leaf.access(),
                                },
                                ObligationStatus::Refuted,
                            );
                            continue;
                        };
                        object.allocation_id.zip(offset).map_or(
                            ObligationStatus::Unknown,
                            |(allocation, offset)| {
                                let key = ResourcePayloadKey::new(offset, leaf.access());
                                self.state
                                    .loan(loan_id)
                                    .map_or(ObligationStatus::Unknown, |loan| {
                                        combine_statuses([
                                            stored_loan_authority_status(
                                                loan,
                                                allocation,
                                                key,
                                                loan_id,
                                                if leaf.mutability() == VirMutability::Const {
                                                    VirLoanKind::Shared
                                                } else {
                                                    VirLoanKind::Mutable
                                                },
                                            ),
                                            loan_activity_access_status(loan.activity()),
                                            no_active_child_status(&self.state, loan_id),
                                        ])
                                    })
                            },
                        )
                    }
                    VirPointerKind::Raw => ObligationStatus::Refuted,
                },
                MovePathState::Moved if guaranteed => ObligationStatus::Proven,
                MovePathState::Available(_) | MovePathState::Moved | MovePathState::Unknown => {
                    ObligationStatus::Unknown
                }
            };
            self.require(
                ResourceObligationKind::ObjectDropPayloadValid {
                    allocation: object.allocation_id,
                    offset_bytes: offset,
                    access: leaf.access(),
                },
                status,
            );
            if let (MovePathState::Available(payload), Some(owner), Some(offset)) =
                (state, object.allocation_id, offset)
            {
                dropped.push((
                    owner,
                    ResourcePayloadKey::new(offset, leaf.access()),
                    leaf.kind(),
                    payload,
                    status,
                ));
            }
        }

        for (owner, key, kind, payload, status) in dropped {
            if status.is_proven() {
                match kind {
                    VirPointerKind::Own => {
                        if let AbstractProvenance::Known(allocation) =
                            payload.pointer().provenance()
                            && let Some(allocation) = self.state.allocation_mut(allocation)
                        {
                            allocation.mark_dead();
                        }
                    }
                    VirPointerKind::Reference => {
                        if let PermissionAuthority::Loan(loan_id) = payload.permission().authority()
                        {
                            self.end_stored_loan_authority(loan_id, owner, key);
                        }
                    }
                    VirPointerKind::Raw => {}
                }
                if let Some(allocation) = self.state.allocation_mut(owner) {
                    let _ = allocation.set_resource_payload(key, MovePathState::Moved)?;
                }
            }
        }
        self.apply_object_deinitialize(&object, &mask)
    }

    fn drop_own(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        condition_id: VirValueId,
    ) -> Result<(), TransferError> {
        match self.require_drop_flag(condition_id)? {
            Some(true) => self.free(pointer_id, permission_id),
            Some(false) | None => Ok(()),
        }
    }

    fn require_drop_flag(
        &mut self,
        condition_id: VirValueId,
    ) -> Result<Option<bool>, TransferError> {
        let condition = bool_fact(&self.state, condition_id)?;
        let value = match condition {
            AbstractBool::True => Some(true),
            AbstractBool::False => Some(false),
            AbstractBool::Unknown => None,
        };
        self.require(
            ResourceObligationKind::DropFlagKnown {
                condition: condition_id,
            },
            if value.is_some() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        );
        Ok(value)
    }

    fn enum_set_discriminant(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
        variant: VirVariantId,
        mode: VirObjectDestinationMode,
    ) -> Result<(), TransferError> {
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Write)?;
        let case = object
            .shape
            .variants()
            .iter()
            .find(|case| case.path().segments().is_empty() && case.variant() == variant)
            .ok_or(TransferError::InvalidValidatedEnumVariant { access, variant })?;
        let tag = ByteSet::single(object_relative_range(case.tag())?);
        // Changing representation must not erase a live payload, even when a
        // malformed producer has already forgotten or overwritten its tag.
        let empty = object_resource_payload_empty_status(&object, self.memory);
        self.require(
            ResourceObligationKind::ObjectResourcePayloadEmpty {
                allocation: object.allocation_id,
                offset_bytes: object.pointer.offset_bytes().exact_value(),
                access,
            },
            empty,
        );
        if !empty.is_proven() {
            return Ok(());
        }
        let previous_mask = match mode {
            VirObjectDestinationMode::Initialize => None,
            VirObjectDestinationMode::Replace => Some(active_object_mask(&object)),
        };

        match mode {
            VirObjectDestinationMode::Initialize => self.require_object_initialization(
                &object,
                &tag,
                InitializationRequirement::Uninitialized,
            ),
            VirObjectDestinationMode::Replace => {
                let mask = previous_mask.as_ref().expect("replace mask is present");
                self.require_active_variants(&object, mask);
                self.require_object_initialization(
                    &object,
                    &tag,
                    InitializationRequirement::Initialized,
                );
                self.require_object_validity(&object, &tag);
                self.require(
                    ResourceObligationKind::ObjectTriviallyDroppable { access },
                    droppable_object_status(self.memory, access),
                );
            }
        }

        let mut retired_payload = ByteSet::new();
        for range in case.value_bytes() {
            retired_payload.insert(object_relative_range(*range)?);
        }
        if let Some(mask) = previous_mask {
            retired_payload = retired_payload.union(&mask.possible_value_bytes);
        }
        for range in tag.ranges() {
            retired_payload.remove(*range);
        }
        self.apply_object_uninitialized(&object, &retired_payload)?;
        self.apply_object_write(&object, &tag, &tag)?;
        if let (Some(allocation_id), Some(base)) = (
            object.allocation_id,
            object.pointer.offset_bytes().exact_value(),
        ) && let Some(allocation) = self.state.allocation_mut(allocation_id)
        {
            if let Some(envelope) = object.envelope {
                allocation.forget_object_state(envelope)?;
            }
            let tracked = allocation.set_active_variant(
                ObjectStateKey::new(base, access),
                ActiveVariantState::Exact(variant),
            )?;
            if !tracked {
                // The effect remains safe, but later active-variant queries
                // must observe Unknown once the precision budget is exhausted.
            }
            // These are empty construction slots, not initialized values or
            // resource authority. Whole observation still checks every active
            // value byte and payload independently.
            for leaf in object.shape.resource_leaves() {
                let _ = allocation.set_resource_payload(
                    ResourcePayloadKey::new(base + leaf.bytes().start_bytes(), leaf.access()),
                    MovePathState::Moved,
                )?;
            }
        }
        Ok(())
    }

    fn enum_discriminant(
        &mut self,
        result: VirValue,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Read)?;
        let root_cases = object
            .shape
            .variants()
            .iter()
            .filter(|case| case.path().segments().is_empty() && case.enum_access() == access)
            .collect::<Vec<_>>();
        let first = root_cases
            .first()
            .copied()
            .ok_or(TransferError::InvalidValidatedMemoryAccess(access))?;
        let tag = ByteSet::single(object_relative_range(first.tag())?);
        if root_cases.iter().any(|case| case.tag() != first.tag()) {
            return Err(TransferError::InvalidValidatedMemoryAccess(access));
        }
        self.require_object_initialization(&object, &tag, InitializationRequirement::Initialized);
        self.require_object_validity(&object, &tag);

        let declared = root_cases
            .iter()
            .map(|case| case.variant())
            .collect::<BTreeSet<_>>();
        let mut possible = object
            .pointer
            .offset_bytes()
            .exact_value()
            .zip(object.allocation.as_ref())
            .and_then(|(base, allocation)| {
                allocation
                    .active_variant(ObjectStateKey::new(base, access))
                    .alternatives()
            })
            .unwrap_or_else(|| declared.clone());
        possible.retain(|variant| declared.contains(variant));
        if possible.is_empty() {
            possible = declared;
        }
        let active = if possible.len() == 1 {
            ActiveVariantState::Exact(*possible.first().expect("one possible variant"))
        } else {
            ActiveVariantState::Alternatives(possible.clone())
        };
        if let (Some(allocation_id), Some(base)) = (
            object.allocation_id,
            object.pointer.offset_bytes().exact_value(),
        ) && let Some(allocation) = self.state.allocation_mut(allocation_id)
        {
            let _ = allocation.set_active_variant(ObjectStateKey::new(base, access), active)?;
        }
        let mut discriminants = root_cases
            .iter()
            .filter(|case| possible.contains(&case.variant()))
            .map(|case| case.discriminant());
        let first_discriminant = discriminants
            .next()
            .ok_or(TransferError::InvalidValidatedMemoryAccess(access))?;
        let (lower, upper) = discriminants.fold(
            (first_discriminant, first_discriminant),
            |(lower, upper), value| (lower.min(value), upper.max(value)),
        );
        let interval = U64Interval::new(lower, upper)
            .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
        self.define(
            result,
            AbstractValue::EnumDiscriminant(EnumDiscriminantFact::new(
                interval,
                object.pointer,
                access,
            )),
        )
    }

    fn require_active_variants(&mut self, object: &ObjectAccessFacts, mask: &ActiveObjectMask) {
        for (site, _, status) in &mask.sites {
            self.require(
                ResourceObligationKind::ObjectActiveVariantKnown {
                    allocation: object.allocation_id,
                    offset_bytes: object
                        .pointer
                        .offset_bytes()
                        .exact_value()
                        .and_then(|base| base.checked_add(site.offset_bytes)),
                    access: site.access,
                },
                *status,
            );
        }
    }

    fn require_object_initialization(
        &mut self,
        object: &ObjectAccessFacts,
        relative_ranges: &ByteSet,
        requirement: InitializationRequirement,
    ) {
        let mut status =
            object
                .allocation
                .as_ref()
                .map_or(ObligationStatus::Unknown, |allocation| {
                    object_ranges_status(object.pointer, relative_ranges, |range| {
                        initialization_status(
                            allocation.initialization().classify(range),
                            requirement,
                        )
                    })
                });
        if matches!(requirement, InitializationRequirement::Initialized)
            && !status.is_proven()
            && self.object_prefix_covers(object)
        {
            status = ObligationStatus::Proven;
        }
        let kind = match requirement {
            InitializationRequirement::Initialized => {
                ResourceObligationKind::ObjectValueBytesInitialized {
                    allocation: object.allocation_id,
                    access: object.envelope,
                    object: object.shape.access(),
                }
            }
            InitializationRequirement::Uninitialized => {
                ResourceObligationKind::ObjectValueBytesUninitialized {
                    allocation: object.allocation_id,
                    access: object.envelope,
                    object: object.shape.access(),
                }
            }
            InitializationRequirement::None => return,
        };
        self.require(kind, status);
    }

    fn require_object_validity(&mut self, object: &ObjectAccessFacts, relative_ranges: &ByteSet) {
        let mut status =
            object
                .allocation
                .as_ref()
                .map_or(ObligationStatus::Unknown, |allocation| {
                    object_ranges_status(object.pointer, relative_ranges, |range| {
                        if allocation.valid_value_bytes().contains(range) {
                            ObligationStatus::Proven
                        } else {
                            ObligationStatus::Unknown
                        }
                    })
                });
        if !status.is_proven() && self.object_prefix_covers(object) {
            status = ObligationStatus::Proven;
        }
        self.require(
            ResourceObligationKind::ObjectRepresentationValid {
                allocation: object.allocation_id,
                access: object.envelope,
                object: object.shape.access(),
            },
            status,
        );
    }

    fn object_prefix_covers(&self, object: &ObjectAccessFacts) -> bool {
        object.allocation_id.is_some_and(|id| {
            self.state.initialized_prefix_covers(
                id,
                object.shape.access(),
                super::relation::range::access_range(object.pointer, object.shape.size_bytes()),
                self.relation_limits,
                &self.relations.queries,
            )
        })
    }

    fn apply_object_write(
        &mut self,
        object: &ObjectAccessFacts,
        possible: &ByteSet,
        guaranteed: &ByteSet,
    ) -> Result<(), TransferError> {
        let Some(allocation_id) = object.allocation_id else {
            return Ok(());
        };
        let Some(allocation) = self.state.allocation_mut(allocation_id) else {
            return Ok(());
        };
        if !possible.is_precise() {
            if let Some(envelope) = object.envelope
                && envelope.end() <= allocation.size_bytes()
            {
                allocation.forget_initialization(envelope)?;
            }
        } else {
            for range in possible.ranges() {
                if let Some(range) = relative_access_envelope(object.pointer.offset_bytes(), *range)
                    && range.end() <= allocation.size_bytes()
                {
                    allocation.forget_initialization(range)?;
                }
            }
        }
        for range in guaranteed.ranges() {
            if let Some(range) = relative_definite_access(object.pointer.offset_bytes(), *range)
                && range.end() <= allocation.size_bytes()
            {
                allocation.mark_initialized(range)?;
                allocation.mark_valid(range)?;
            }
        }
        Ok(())
    }

    fn apply_object_deinitialize(
        &mut self,
        object: &ObjectAccessFacts,
        mask: &ActiveObjectMask,
    ) -> Result<(), TransferError> {
        let Some(allocation_id) = object.allocation_id else {
            return Ok(());
        };
        let Some(allocation) = self.state.allocation_mut(allocation_id) else {
            return Ok(());
        };
        let empty_payloads = empty_resource_paths(allocation);
        if !mask.possible_value_bytes.is_precise() {
            if let Some(envelope) = object.envelope
                && envelope.end() <= allocation.size_bytes()
            {
                allocation.forget_initialization(envelope)?;
            }
        } else {
            for range in mask.possible_value_bytes.ranges() {
                if let Some(range) = relative_access_envelope(object.pointer.offset_bytes(), *range)
                    && range.end() <= allocation.size_bytes()
                {
                    allocation.forget_initialization(range)?;
                }
            }
        }
        // Forget the object-wide cache before installing definite retirement
        // facts. Doing this afterwards erased Moved payload paths established
        // by mark_uninitialized, making safe nested refill look Unknown.
        if let Some(envelope) = object.envelope
            && envelope.end() <= allocation.size_bytes()
        {
            allocation.forget_object_state(envelope)?;
        }
        for range in mask.guaranteed_value_bytes.ranges() {
            if let Some(range) = relative_definite_access(object.pointer.offset_bytes(), *range)
                && range.end() <= allocation.size_bytes()
            {
                allocation.mark_uninitialized(range)?;
            }
        }
        restore_empty_resource_paths(allocation, &empty_payloads)?;
        Ok(())
    }

    fn apply_object_uninitialized(
        &mut self,
        object: &ObjectAccessFacts,
        relative_ranges: &ByteSet,
    ) -> Result<(), TransferError> {
        let Some(allocation_id) = object.allocation_id else {
            return Ok(());
        };
        let Some(allocation) = self.state.allocation_mut(allocation_id) else {
            return Ok(());
        };
        for range in relative_ranges.ranges() {
            if let Some(range) = relative_definite_access(object.pointer.offset_bytes(), *range)
                && range.end() <= allocation.size_bytes()
            {
                allocation.mark_uninitialized(range)?;
            }
        }
        Ok(())
    }

    fn copy_active_variants(
        &mut self,
        source: &ObjectAccessFacts,
        destination: &ObjectAccessFacts,
        source_mask: &ActiveObjectMask,
    ) -> Result<(), TransferError> {
        let (Some(destination_id), Some(destination_base), Some(envelope)) = (
            destination.allocation_id,
            destination.pointer.offset_bytes().exact_value(),
            destination.envelope,
        ) else {
            return Ok(());
        };
        let Some(allocation) = self.state.allocation_mut(destination_id) else {
            return Ok(());
        };
        if envelope.end() <= allocation.size_bytes() {
            allocation.forget_object_state(envelope)?;
        }
        if source.allocation_id.is_none() || source.pointer.offset_bytes().exact_value().is_none() {
            return Ok(());
        }
        for (site, state, status) in &source_mask.sites {
            if *status != ObligationStatus::Proven || matches!(state, ActiveVariantState::Unknown) {
                continue;
            }
            let Some(offset) = destination_base.checked_add(site.offset_bytes) else {
                continue;
            };
            let _ = allocation
                .set_active_variant(ObjectStateKey::new(offset, site.access), state.clone())?;
        }
        Ok(())
    }

    fn free(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, pointer_id)?;
        let permission = permission_fact(&self.state, permission_id)?;
        self.require(
            ResourceObligationKind::PointerProvenanceKnown {
                pointer: pointer_id,
            },
            known_provenance_status(pointer.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerAtAllocationBase {
                pointer: pointer_id,
            },
            base_pointer_status(pointer.offset_bytes()),
        );
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: permission_id,
            },
            permission_availability_status(permission.availability()),
        );
        self.require(
            ResourceObligationKind::PermissionCanFree {
                permission: permission_id,
            },
            free_capability_status(permission.free_capability()),
        );
        let full_access = match pointer.provenance() {
            AbstractProvenance::Known(allocation) => self
                .state
                .allocation(allocation)
                .and_then(|allocation| ByteRange::new(0, allocation.size_bytes()).ok()),
            AbstractProvenance::Unknown => None,
        };
        let (loan, loan_status) = permission_loan_access_status(
            &self.state,
            permission_id,
            permission,
            LoanAccess::whole(pointer, full_access, AccessPermission::Write),
            self.relation_limits,
            &self.relations,
        );
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan,
                permission: permission_id,
                access: full_access,
                required: AccessPermission::Write,
            },
            loan_status,
        );

        if let AbstractProvenance::Known(allocation_id) = pointer.provenance() {
            let allocation = self.state.allocation(allocation_id).cloned();
            self.require(
                ResourceObligationKind::AllocationTracked {
                    allocation: allocation_id,
                },
                if allocation.is_some() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
            self.require(
                ResourceObligationKind::PermissionMatchesAllocation {
                    permission: permission_id,
                    allocation: allocation_id,
                },
                provenance_match_status(permission.provenance(), allocation_id),
            );
            if let Some(allocation) = allocation {
                self.require(
                    ResourceObligationKind::AllocationLive {
                        allocation: allocation_id,
                    },
                    liveness_status(allocation.liveness()),
                );
                self.require(
                    ResourceObligationKind::AllocationOwned {
                        allocation: allocation_id,
                    },
                    ownership_status(allocation.ownership()),
                );
                self.require(
                    ResourceObligationKind::PermissionCoversAllocation {
                        permission: permission_id,
                        allocation: allocation_id,
                    },
                    full_permission_status(permission.range(), allocation.size_bytes()),
                );
                self.require(
                    ResourceObligationKind::AllocationResourcePayloadEmpty {
                        allocation: allocation_id,
                    },
                    allocation_resource_payload_empty_status(&allocation),
                );
                if let Some(allocation) = self.state.allocation_mut(allocation_id) {
                    allocation.mark_dead();
                }
            }
        }
        mark_permission_consumed(&mut self.state, permission_id)?;
        Ok(())
    }

    fn permission_split(
        &mut self,
        left_result: VirValue,
        right_result: VirValue,
        source_id: VirValueId,
        split_id: VirValueId,
    ) -> Result<(), TransferError> {
        let source = permission_fact(&self.state, source_id)?;
        let split_at = word_fact(&self.state, split_id)?;
        let split_expression = word_expression(&self.state, split_id, split_at);
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: source_id,
            },
            permission_availability_status(source.availability()),
        );
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: match source.authority() {
                    PermissionAuthority::Loan(loan) => Some(loan),
                    PermissionAuthority::Owner | PermissionAuthority::Unknown => None,
                },
                permission: source_id,
                access: exact_abstract_range(source.range()),
                required: AccessPermission::Read,
            },
            owner_authority_status(source.authority()),
        );
        self.require(
            ResourceObligationKind::PermissionSplitPointInRange {
                permission: source_id,
                split_at,
            },
            split_status(source.range(), split_at, split_expression),
        );

        let (left_range, right_range) = split_ranges(source.range(), split_at, split_expression)?;
        mark_permission_consumed(&mut self.state, source_id)?;
        self.define(
            left_result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    source.provenance(),
                    left_range,
                    source.access(),
                    source.free_capability(),
                )
                .with_authority(source.authority()),
            ),
        )?;
        self.define(
            right_result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    source.provenance(),
                    right_range,
                    source.access(),
                    source.free_capability(),
                )
                .with_authority(source.authority()),
            ),
        )
    }

    fn permission_join(
        &mut self,
        result: VirValue,
        left_id: VirValueId,
        right_id: VirValueId,
    ) -> Result<(), TransferError> {
        let left = permission_fact(&self.state, left_id)?;
        let right = permission_fact(&self.state, right_id)?;
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: left_id,
            },
            permission_availability_status(left.availability()),
        );
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: right_id,
            },
            permission_availability_status(right.availability()),
        );
        self.require(
            ResourceObligationKind::PermissionOperandsDistinct {
                left: left_id,
                right: right_id,
            },
            if left_id == right_id {
                ObligationStatus::Refuted
            } else {
                ObligationStatus::Proven
            },
        );
        let (compatibility, joined_range) = permission_join_status(left, right)?;
        self.require(
            ResourceObligationKind::PermissionJoinCompatible {
                left: left_id,
                right: right_id,
            },
            compatibility,
        );

        mark_permission_consumed(&mut self.state, left_id)?;
        if right_id != left_id {
            mark_permission_consumed(&mut self.state, right_id)?;
        }
        self.define(
            result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    left.provenance().join(right.provenance()),
                    joined_range,
                    left.access().join(right.access()),
                    left.free_capability().join(right.free_capability()),
                )
                .with_authority(left.authority().join(right.authority())),
            ),
        )
    }

    fn permission_move(
        &mut self,
        result: VirValue,
        source_id: VirValueId,
    ) -> Result<(), TransferError> {
        let source = permission_fact(&self.state, source_id)?;
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: source_id,
            },
            permission_availability_status(source.availability()),
        );
        mark_permission_consumed(&mut self.state, source_id)?;
        self.move_loan_authority(source.authority(), source_id, result.id);
        self.define(
            result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    source.provenance(),
                    source.range(),
                    source.access(),
                    source.free_capability(),
                )
                .with_authority(source.authority()),
            ),
        )
    }

    fn loan_begin(
        &mut self,
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let context = self
            .loan_context
            .ok_or(TransferError::MissingLoanTransferContext)?;
        let range = loan_range(effect)?;
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        let source_status = combine_statuses([
            self.require_loan_source(effect, pointer, permission, range),
            self.require_loan_value(effect, pointer, range)?,
        ]);
        let instance_status = self.require_previous_loan_instance_ended(effect.loan);
        let authority_status = owner_authority_status(permission.authority());
        let conflict_status = loan_creation_compatibility(
            &self.state,
            effect,
            None,
            self.borrow_footprint(effect, pointer, range),
            self.relation_limits,
            &self.relations,
        );
        let compatibility = combine_statuses([authority_status, conflict_status]);
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: Some(effect.loan),
                permission: effect.source_permission,
                access: Some(range),
                required: loan_access(effect.kind),
            },
            compatibility,
        );

        let budget_status = self.require_active_loan_budget(effect.loan, context.limits);
        let exact = [source_status, instance_status, compatibility, budget_status]
            .into_iter()
            .all(ObligationStatus::is_proven);
        let activity = if exact {
            LoanActivity::Active
        } else {
            LoanActivity::MaybeActive
        };
        let tracked = budget_status.is_proven() && instance_status.is_proven();
        if tracked {
            let loan = AbstractLoan::new(
                pointer.provenance(),
                range,
                effect.kind,
                effect.region,
                effect.parent,
                activity,
            )
            .with_footprint(self.borrow_footprint(effect, pointer, range));
            self.state.define_next_loan_instance(
                effect.loan,
                if exact {
                    loan.with_authority(permission_result.id)
                } else {
                    loan
                },
            )?;
        }
        self.define_loan_results(effect, pointer, reference_result, permission_result, exact)
    }

    fn loan_alias_shared(
        &mut self,
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let context = self
            .loan_context
            .ok_or(TransferError::MissingLoanTransferContext)?;
        let range = loan_range(effect)?;
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        let source_status = combine_statuses([
            self.require_loan_source(effect, pointer, permission, range),
            self.require_loan_value(effect, pointer, range)?,
        ]);
        let compatibility =
            self.state
                .loan(effect.loan)
                .map_or(ObligationStatus::Unknown, |loan| {
                    combine_statuses([
                        tracked_loan_authority_status(
                            loan,
                            effect.source_permission,
                            permission.authority(),
                            effect.loan,
                        ),
                        loan_activity_access_status(loan.activity()),
                        if loan.kind() == VirLoanKind::Shared {
                            ObligationStatus::Proven
                        } else {
                            ObligationStatus::Refuted
                        },
                        loan_metadata_status(loan, effect, pointer.provenance(), range),
                    ])
                });
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: Some(effect.loan),
                permission: effect.source_permission,
                access: Some(range),
                required: AccessPermission::Read,
            },
            compatibility,
        );
        let alias_status = self.require_alias_budget(effect.loan, context.limits);
        let tracked = [source_status, compatibility, alias_status]
            .into_iter()
            .all(ObligationStatus::is_proven);
        if !tracked && let Some(loan) = self.state.loan_mut(effect.loan) {
            loan.set_activity(LoanActivity::MaybeActive);
        }
        if tracked && let Some(loan) = self.state.loan_mut(effect.loan) {
            loan.add_authority(permission_result.id);
        }
        self.define_loan_results(
            effect,
            pointer,
            reference_result,
            permission_result,
            tracked,
        )
    }

    fn loan_alias_authority(
        &mut self,
        effect: VirLoanAuthorityEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        if let Some(effect) = self.resolve_authority_effect(effect, permission) {
            return self.loan_alias_shared(effect, reference_result, permission_result);
        }
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: None,
                permission: effect.source_permission,
                access: None,
                required: AccessPermission::Read,
            },
            ObligationStatus::Unknown,
        );
        let pointee = reference_pointee(self.memory, effect.reference)?;
        self.define(
            reference_result,
            AbstractValue::Pointer(pointer.with_memory_access(Some(pointee))),
        )?;
        self.define(
            permission_result,
            AbstractValue::Permission(
                permission
                    .with_availability(PermissionAvailability::Available)
                    .with_authority(PermissionAuthority::Unknown),
            ),
        )
    }

    fn loan_reborrow_authority(
        &mut self,
        loan: VirLoanId,
        region: crate::VirBorrowRegionId,
        effect: VirLoanAuthorityEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        let kind = match self.memory.kind(effect.reference.ty) {
            Some(VirMemoryTypeKind::Slice {
                mutability: VirMutability::Mutable,
                ..
            })
            | Some(VirMemoryTypeKind::Pointer {
                mutability: VirMutability::Mutable,
                ..
            }) => VirLoanKind::Mutable,
            _ => VirLoanKind::Shared,
        };
        if let Some(parent) = self.resolve_authority_effect(effect, permission) {
            let access = reference_pointee(self.memory, effect.reference)?;
            let width = self
                .memory
                .object_shape(access)
                .map_err(|_| TransferError::InvalidDerivedRange)?
                .size_bytes();
            let slice = matches!(
                self.memory.kind(effect.reference.ty),
                Some(VirMemoryTypeKind::Slice { .. })
            );
            let range = if slice {
                pointer.slice_footprint().map(|f| f.envelope)
            } else {
                access_envelope(pointer.offset_bytes(), width)
            };
            if let Some(range) = range {
                return self.loan_reborrow(
                    VirLoanEffect {
                        loan,
                        kind,
                        region,
                        parent: Some(parent.loan),
                        source_pointer: effect.source_pointer,
                        source_permission: effect.source_permission,
                        reference: effect.reference,
                        range: crate::VirLoanRange {
                            start_bytes: range.start(),
                            end_bytes: range.end(),
                        },
                        origin: effect.origin,
                    },
                    reference_result,
                    permission_result,
                );
            }
        }
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: Some(loan),
                permission: effect.source_permission,
                access: None,
                required: loan_access(kind),
            },
            ObligationStatus::Unknown,
        );
        self.define(reference_result, AbstractValue::Pointer(pointer))?;
        self.define(
            permission_result,
            AbstractValue::Permission(fresh_unknown_permission()),
        )
    }

    fn loan_reborrow(
        &mut self,
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let context = self
            .loan_context
            .ok_or(TransferError::MissingLoanTransferContext)?;
        let range = loan_range(effect)?;
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        let source_status = combine_statuses([
            self.require_loan_source(effect, pointer, permission, range),
            self.require_loan_value(effect, pointer, range)?,
        ]);
        let instance_status = self.require_previous_loan_instance_ended(effect.loan);
        let parent_id = effect
            .parent
            .ok_or(TransferError::InvalidValidatedLoan(effect.loan))?;
        let parent = self.state.loan(parent_id);
        let parent_region = parent.map(AbstractLoan::region);
        let shared_child = parent.is_some_and(|parent| {
            parent.kind() == VirLoanKind::Shared && effect.kind == VirLoanKind::Shared
        });
        let parent_status = parent.map_or(ObligationStatus::Unknown, |parent| {
            let authority = tracked_loan_authority_status(
                parent,
                effect.source_permission,
                permission.authority(),
                parent_id,
            );
            let activity = match parent.activity() {
                LoanActivity::Active | LoanActivity::Suspended => ObligationStatus::Proven,
                LoanActivity::MaybeActive => ObligationStatus::Unknown,
                LoanActivity::Ended => ObligationStatus::Refuted,
            };
            let containment = combine_statuses([
                parent_contains_child_status(parent, effect, pointer.provenance(), range),
                self.borrow_footprint(effect, pointer, range)
                    .map_or(ObligationStatus::Unknown, |f| {
                        self.range_contains(parent.actual_range(), f.range)
                    }),
            ]);
            combine_statuses([authority, activity, containment])
        });
        self.require(
            ResourceObligationKind::LoanParentActive {
                loan: effect.loan,
                parent: parent_id,
            },
            parent_status,
        );

        let region_status = if context
            .borrows
            .constraints()
            .iter()
            .filter(|constraint| constraint.owner == context.function)
            .count()
            > context.limits.max_region_constraints
        {
            self.state
                .mark_loan_precision_loss(LoanPrecisionLoss::RegionConstraintBudget);
            ObligationStatus::Unknown
        } else {
            match parent_region.and_then(|parent_region| {
                context.borrows.includes(
                    effect.region,
                    parent_region,
                    context.limits.max_region_constraints,
                )
            }) {
                Some(true) => ObligationStatus::Proven,
                Some(false) => ObligationStatus::Refuted,
                None => {
                    if parent_region.is_some() {
                        self.state
                            .mark_loan_precision_loss(LoanPrecisionLoss::RegionConstraintBudget);
                    }
                    ObligationStatus::Unknown
                }
            }
        };
        self.require(
            ResourceObligationKind::LoanRegionIncluded {
                loan: effect.loan,
                parent: parent_id,
            },
            region_status,
        );
        let depth_status = self.require_reborrow_depth(effect.loan, parent_id, context.limits);
        let conflict_status = loan_creation_compatibility(
            &self.state,
            effect,
            Some(parent_id),
            self.borrow_footprint(effect, pointer, range),
            self.relation_limits,
            &self.relations,
        );
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: Some(effect.loan),
                permission: effect.source_permission,
                access: Some(range),
                required: loan_access(effect.kind),
            },
            conflict_status,
        );
        let budget_status = self.require_active_loan_budget(effect.loan, context.limits);
        let exact = [
            source_status,
            instance_status,
            parent_status,
            region_status,
            depth_status,
            conflict_status,
            budget_status,
        ]
        .into_iter()
        .all(ObligationStatus::is_proven);
        if let Some(parent) = self.state.loan_mut(parent_id) {
            parent.set_activity(if exact && shared_child {
                LoanActivity::Active
            } else if exact {
                LoanActivity::Suspended
            } else {
                LoanActivity::MaybeActive
            });
        }
        let tracked = budget_status.is_proven() && instance_status.is_proven();
        if tracked {
            let loan = AbstractLoan::new(
                pointer.provenance(),
                range,
                effect.kind,
                effect.region,
                effect.parent,
                if exact {
                    LoanActivity::Active
                } else {
                    LoanActivity::MaybeActive
                },
            )
            .with_footprint(self.borrow_footprint(effect, pointer, range));
            self.state.define_next_loan_instance(
                effect.loan,
                if exact {
                    loan.with_authority(permission_result.id)
                } else {
                    loan
                },
            )?;
        }
        self.define_loan_results(effect, pointer, reference_result, permission_result, exact)
    }

    fn loan_end(&mut self, effect: VirLoanEffect) -> Result<(), TransferError> {
        let _context = self
            .loan_context
            .ok_or(TransferError::MissingLoanTransferContext)?;
        let range = loan_range(effect)?;
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        // Ending an authority is not a memory access and does not reevaluate
        // its selection. Lost SSA bounds must not keep a valid loan alive.
        let source_status = permission_availability_status(permission.availability());
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: effect.source_permission,
            },
            source_status,
        );
        let end_status = self
            .state
            .loan(effect.loan)
            .map_or(ObligationStatus::Unknown, |loan| {
                combine_statuses([
                    tracked_loan_authority_status(
                        loan,
                        effect.source_permission,
                        permission.authority(),
                        effect.loan,
                    ),
                    loan_activity_access_status(loan.activity()),
                    loan_metadata_status(loan, effect, pointer.provenance(), range),
                    no_active_child_status(&self.state, effect.loan),
                ])
            });
        let exact = source_status.is_proven() && end_status.is_proven();
        self.require(
            ResourceObligationKind::LoanEndedExactlyOnce { loan: effect.loan },
            end_status,
        );
        mark_permission_consumed(&mut self.state, effect.source_permission)?;
        let remaining =
            self.state
                .loan_mut(effect.loan)
                .map_or(ObligationStatus::Unknown, |loan| {
                    let removed = loan.remove_authority(effect.source_permission);
                    match (removed, loan.authorities().is_empty()) {
                        (true, true) => ObligationStatus::Proven,
                        (true, false) => ObligationStatus::Refuted,
                        (false, _) => ObligationStatus::Unknown,
                    }
                });
        let parent_id = self.state.loan(effect.loan).and_then(|loan| loan.parent());
        if let Some(loan) = self.state.loan_mut(effect.loan) {
            loan.set_activity(if exact {
                match remaining {
                    ObligationStatus::Proven => LoanActivity::Ended,
                    ObligationStatus::Refuted => LoanActivity::Active,
                    ObligationStatus::Unknown => LoanActivity::MaybeActive,
                }
            } else {
                LoanActivity::MaybeActive
            });
        }
        if exact && remaining.is_proven() {
            self.restore_parent_after_child(effect.loan, parent_id);
        }
        Ok(())
    }

    fn loan_end_authority(&mut self, effect: VirLoanAuthorityEffect) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        if let Some(resolved) = self.resolve_authority_effect(effect, permission) {
            let range = loan_range(resolved)?;
            let availability = permission_availability_status(permission.availability());
            self.require(
                ResourceObligationKind::PermissionAvailable {
                    permission: effect.source_permission,
                },
                availability,
            );
            let no_active_child = no_active_child_status(&self.state, resolved.loan);
            let authority =
                self.state
                    .loan(resolved.loan)
                    .map_or(ObligationStatus::Unknown, |loan| {
                        combine_statuses([
                            tracked_loan_authority_status(
                                loan,
                                effect.source_permission,
                                permission.authority(),
                                resolved.loan,
                            ),
                            loan_activity_access_status(loan.activity()),
                            loan_metadata_status(loan, resolved, pointer.provenance(), range),
                            if loan.authorities().len() > 1 {
                                ObligationStatus::Proven
                            } else {
                                no_active_child
                            },
                        ])
                    });
            self.require(
                ResourceObligationKind::LoanCompatible {
                    loan: Some(resolved.loan),
                    permission: effect.source_permission,
                    access: Some(range),
                    required: AccessPermission::Read,
                },
                authority,
            );
            mark_permission_consumed(&mut self.state, effect.source_permission)?;
            let parent = self
                .state
                .loan(resolved.loan)
                .and_then(AbstractLoan::parent);
            let ended = self.state.loan_mut(resolved.loan).is_some_and(|loan| {
                let removed = loan.remove_authority(effect.source_permission);
                if !removed {
                    loan.set_activity(LoanActivity::MaybeActive);
                    return false;
                }
                if loan.authorities().is_empty() {
                    loan.set_activity(LoanActivity::Ended);
                    true
                } else {
                    false
                }
            });
            if ended {
                self.restore_parent_after_child(resolved.loan, parent);
            }
            return Ok(());
        }
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: None,
                permission: effect.source_permission,
                access: None,
                required: AccessPermission::Read,
            },
            ObligationStatus::Unknown,
        );
        mark_permission_consumed(&mut self.state, effect.source_permission)
    }

    fn end_stored_loan_authority(
        &mut self,
        loan_id: VirLoanId,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    ) {
        let parent_id = self.state.loan(loan_id).and_then(AbstractLoan::parent);
        let ended = self.state.loan_mut(loan_id).is_some_and(|loan| {
            loan.remove_stored_authority(allocation, payload) && loan.authorities().is_empty()
        });
        if let Some(loan) = self.state.loan_mut(loan_id) {
            loan.set_activity(if ended {
                LoanActivity::Ended
            } else {
                LoanActivity::Active
            });
        }
        if ended {
            self.restore_parent_after_child(loan_id, parent_id);
        }
    }

    fn resolve_authority_effect(
        &self,
        effect: VirLoanAuthorityEffect,
        permission: AbstractPermission,
    ) -> Option<VirLoanEffect> {
        let PermissionAuthority::Loan(loan_id) = permission.authority() else {
            return None;
        };
        let loan = self.state.loan(loan_id)?;
        Some(VirLoanEffect {
            loan: loan_id,
            kind: loan.kind(),
            region: loan.region(),
            parent: loan.parent(),
            source_pointer: effect.source_pointer,
            source_permission: effect.source_permission,
            reference: effect.reference,
            range: crate::VirLoanRange {
                start_bytes: loan.range().start(),
                end_bytes: loan.range().end(),
            },
            origin: effect.origin,
        })
    }

    fn require_previous_loan_instance_ended(&mut self, loan: VirLoanId) -> ObligationStatus {
        let status = self
            .state
            .loan(loan)
            .map_or(ObligationStatus::Proven, |previous| {
                match previous.activity() {
                    LoanActivity::Ended => ObligationStatus::Proven,
                    LoanActivity::Active | LoanActivity::Suspended => ObligationStatus::Refuted,
                    LoanActivity::MaybeActive => ObligationStatus::Unknown,
                }
            });
        self.require(
            ResourceObligationKind::LoanEndedExactlyOnce { loan },
            status,
        );
        status
    }

    fn move_loan_authority(
        &mut self,
        authority: PermissionAuthority,
        source: VirValueId,
        result: VirValueId,
    ) {
        let PermissionAuthority::Loan(loan_id) = authority else {
            return;
        };
        let Some(loan) = self.state.loan_mut(loan_id) else {
            return;
        };
        if !loan.move_authority(source, result) {
            loan.set_activity(LoanActivity::MaybeActive);
        }
    }

    fn define_loan_results(
        &mut self,
        effect: VirLoanEffect,
        pointer: AbstractPointer,
        reference_result: VirValue,
        permission_result: VirValue,
        tracked: bool,
    ) -> Result<(), TransferError> {
        let access = match reference_result.ty {
            VirType::Pointer { access } => access,
            _ => return Err(TransferError::InvalidValidatedLoan(effect.loan)),
        };
        self.define(
            reference_result,
            AbstractValue::Pointer(pointer.with_memory_access(Some(access))),
        )?;
        let range = self
            .state
            .loan(effect.loan)
            .map_or(AbstractByteRange::Unknown, AbstractLoan::actual_range);
        let permission = AbstractPermission::new(
            pointer.provenance(),
            range,
            loan_access(effect.kind),
            FreeCapability::No,
        )
        .with_authority(if tracked {
            PermissionAuthority::Loan(effect.loan)
        } else {
            PermissionAuthority::Unknown
        });
        self.define(permission_result, AbstractValue::Permission(permission))
    }

    /// Formation checks value state independently of loan authority. Ending a
    /// loan deliberately does not use this check: ending cannot manufacture T.
    fn require_loan_value(
        &mut self,
        effect: VirLoanEffect,
        pointer: AbstractPointer,
        range: ByteRange,
    ) -> Result<ObligationStatus, TransferError> {
        let start = self.obligations.len();
        let footprint = self.borrow_footprint(effect, pointer, range);
        let range = footprint.map_or(range, |f| f.envelope);
        let access = reference_pointee(self.memory, effect.reference)?;
        let slice = matches!(
            self.memory.kind(effect.reference.ty),
            Some(VirMemoryTypeKind::Slice { .. })
        );
        let shape = self
            .memory
            .object_shape(access)
            .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
        let stride = shape.size_bytes();
        let domain_status = self.require_domain_range(
            effect.source_pointer,
            pointer,
            if slice {
                footprint.map_or(AbstractByteRange::Exact(range), |f| f.range)
            } else {
                pointer_range(pointer, stride)
            },
        );
        let allocation_id = match pointer.provenance() {
            AbstractProvenance::Known(id) => Some(id),
            AbstractProvenance::Unknown => None,
        };
        let allocation = allocation_id.and_then(|id| self.state.allocation(id));
        let bounds = allocation.map_or(ObligationStatus::Unknown, |allocation| {
            if range.end() <= allocation.size_bytes() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Refuted
            }
        });
        let alignment = allocation.map_or(ObligationStatus::Unknown, |allocation| {
            object_alignment_status(pointer, allocation, shape.alignment())
        });
        let live = allocation.map_or(ObligationStatus::Unknown, |allocation| {
            liveness_status(allocation.liveness())
        });
        let prefix_complete = allocation_id.is_some_and(|id| {
            self.state.initialized_prefix_covers(
                id,
                access,
                footprint.map_or(AbstractByteRange::Unknown, |f| f.range),
                self.relation_limits,
                &self.relations.queries,
            )
        });
        let complete_trivial = slice
            && shape.resource_leaves().is_empty()
            && shape.variants().is_empty()
            && allocation.is_some_and(|allocation| {
                allocation.initialization().classify(range) == InitializationClass::Initialized
                    && allocation.valid_value_bytes().contains(range)
            });
        self.require(
            ResourceObligationKind::ObjectAllocationLive {
                pointer: effect.source_pointer,
                allocation: allocation_id,
            },
            live,
        );
        self.require(
            ResourceObligationKind::ObjectWithinBounds {
                pointer: effect.source_pointer,
                allocation: allocation_id,
                access: Some(range),
                size_bytes: range.length(),
            },
            bounds,
        );
        self.require(
            ResourceObligationKind::ObjectAligned {
                pointer: effect.source_pointer,
                required_alignment: shape.alignment(),
            },
            alignment,
        );
        // A complete trivial byte envelope proves all its possible elements
        // without enumerating a signature-owned, unknown-length slice.
        if complete_trivial || prefix_complete {
            self.require(
                ResourceObligationKind::MemoryInitialized {
                    allocation: allocation_id.expect("complete allocation"),
                    access: Some(range),
                },
                ObligationStatus::Proven,
            );
            self.require(
                ResourceObligationKind::ObjectRepresentationValid {
                    allocation: allocation_id,
                    access: Some(range),
                    object: access,
                },
                ObligationStatus::Proven,
            );
            return Ok(combine_statuses([bounds, alignment, live, domain_status]));
        }
        // Slice effects describe a conservative envelope. Check every element
        // in that envelope, excluding each element's padding, not raw bytes.
        let count = if slice && stride != 0 {
            range.length() / stride
        } else {
            1
        };
        if (slice && (stride == 0 || !range.length().is_multiple_of(stride)))
            || count > crate::vir::VIR_OBJECT_SHAPE_MAX_NODES as u64
        {
            self.require(
                ResourceObligationKind::ObjectRepresentationValid {
                    allocation: allocation_id,
                    access: Some(range),
                    object: access,
                },
                ObligationStatus::Unknown,
            );
        } else {
            let offsets = if slice {
                Some(
                    (0..count)
                        .map(|index| range.start() + index * stride)
                        .collect::<Vec<_>>(),
                )
            } else {
                pointer.object_offsets().candidates()
            };
            let candidates = offsets.map_or_else(
                || vec![pointer],
                |offsets| {
                    offsets
                        .into_iter()
                        .map(|offset| {
                            AbstractPointer::new(
                                pointer.provenance(),
                                U64Interval::exact(offset),
                                pointer.alignment(),
                            )
                            .with_memory_access(pointer.memory_access())
                        })
                        .collect()
                },
            );
            for selected in candidates {
                // Value validity is checked conservatively for every possible
                // selected object. Permission for the ACTUAL symbolic range
                // is checked separately by require_loan_source, not widened
                // to cover every candidate in this envelope.
                let object = ObjectAccessFacts {
                    pointer: selected,
                    allocation_id,
                    allocation: allocation_id.and_then(|id| self.state.allocation(id).cloned()),
                    envelope: access_envelope(selected.offset_bytes(), stride),
                    shape: shape.clone(),
                };
                if let Some(allocation) = &object.allocation {
                    self.active_variant_access_obligations(
                        effect.source_pointer,
                        selected,
                        allocation,
                        access,
                        stride,
                    )?;
                }
                let mask = active_object_mask(&object);
                self.require_active_variants(&object, &mask);
                self.require_object_initialization(
                    &object,
                    &mask.possible_value_bytes,
                    InitializationRequirement::Initialized,
                );
                self.require_object_validity(&object, &mask.possible_value_bytes);
                self.require_object_resource_payloads(&object, &mask);
            }
        }
        Ok(self.obligations[start..]
            .iter()
            .fold(ObligationStatus::Proven, |status, obligation| {
                combine_statuses([status, obligation.status])
            }))
    }

    fn require_loan_source(
        &mut self,
        effect: VirLoanEffect,
        pointer: AbstractPointer,
        permission: AbstractPermission,
        range: ByteRange,
    ) -> ObligationStatus {
        let slice_reference = matches!(
            self.memory.kind(effect.reference.ty),
            Some(VirMemoryTypeKind::Slice { .. })
        );
        let expected_access = match self.memory.kind(effect.reference.ty) {
            Some(VirMemoryTypeKind::Pointer {
                pointee,
                kind: VirPointerKind::Reference,
                ..
            }) => self.memory.access(*pointee),
            Some(VirMemoryTypeKind::Slice { element, .. }) => self.memory.access(*element),
            _ => None,
        };
        let memory_access = expected_access.map_or(ObligationStatus::Refuted, |expected| {
            let status = memory_access_status(pointer.memory_access(), expected);
            self.require(
                ResourceObligationKind::PointerMemoryAccessMatches {
                    pointer: effect.source_pointer,
                    expected,
                    found: pointer.memory_access(),
                },
                status,
            );
            status
        });
        self.require(
            ResourceObligationKind::PointerProvenanceKnown {
                pointer: effect.source_pointer,
            },
            known_provenance_status(pointer.provenance()),
        );
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: effect.source_permission,
            },
            permission_availability_status(permission.availability()),
        );
        let provenance = match pointer.provenance() {
            AbstractProvenance::Known(allocation) => {
                self.require(
                    ResourceObligationKind::PermissionMatchesAllocation {
                        permission: effect.source_permission,
                        allocation,
                    },
                    provenance_match_status(permission.provenance(), allocation),
                );
                self.require(
                    ResourceObligationKind::AllocationTracked { allocation },
                    if self.state.allocation(allocation).is_some() {
                        ObligationStatus::Proven
                    } else {
                        ObligationStatus::Unknown
                    },
                );
                self.require(
                    ResourceObligationKind::AllocationLive { allocation },
                    self.state
                        .allocation(allocation)
                        .map_or(ObligationStatus::Unknown, |allocation| {
                            liveness_status(allocation.liveness())
                        }),
                );
                provenance_match_status(permission.provenance(), allocation)
            }
            AbstractProvenance::Unknown => ObligationStatus::Unknown,
        };
        let footprint = self.borrow_footprint(effect, pointer, range);
        let range_status = combine_statuses([
            if slice_reference {
                pointer_within_slice_range_status(pointer, range)
            } else {
                pointer_within_range_status(pointer, range)
            },
            footprint.map_or(ObligationStatus::Unknown, |f| {
                combine_statuses([
                    if range.contains(f.envelope) {
                        ObligationStatus::Proven
                    } else {
                        ObligationStatus::Refuted
                    },
                    self.range_contains(permission.range(), f.range),
                ])
            }),
            provenance,
        ]);
        self.require(
            ResourceObligationKind::LoanRangeContained {
                loan: effect.loan,
                permission: effect.source_permission,
                range,
            },
            range_status,
        );
        if effect.kind == VirLoanKind::Mutable {
            self.require(
                ResourceObligationKind::PermissionWritable {
                    permission: effect.source_permission,
                },
                permission_writable_status(permission.access()),
            );
        }
        combine_statuses([
            memory_access,
            known_provenance_status(pointer.provenance()),
            permission_availability_status(permission.availability()),
            range_status,
            if effect.kind == VirLoanKind::Mutable {
                permission_writable_status(permission.access())
            } else {
                ObligationStatus::Proven
            },
        ])
    }

    fn require_active_loan_budget(
        &mut self,
        loan: VirLoanId,
        limits: LoanTransferLimits,
    ) -> ObligationStatus {
        let active = self
            .state
            .loans()
            .values()
            .filter(|loan| !matches!(loan.activity(), LoanActivity::Ended))
            .count();
        let status = if active < limits.max_active_loans {
            ObligationStatus::Proven
        } else {
            self.state
                .mark_loan_precision_loss(LoanPrecisionLoss::ActiveLoanBudget);
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::LoanWithinBudget {
                loan,
                limit: limits.max_active_loans,
            },
            status,
        );
        status
    }

    fn require_alias_budget(
        &mut self,
        loan: VirLoanId,
        limits: LoanTransferLimits,
    ) -> ObligationStatus {
        let aliases = available_loan_authorities(&self.state, loan);
        let status = if aliases < limits.max_aliases_per_loan {
            ObligationStatus::Proven
        } else {
            self.state
                .mark_loan_precision_loss(LoanPrecisionLoss::LoanAliasBudget);
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::LoanAliasWithinBudget {
                loan,
                limit: limits.max_aliases_per_loan,
            },
            status,
        );
        status
    }

    fn require_reborrow_depth(
        &mut self,
        loan: VirLoanId,
        parent: VirLoanId,
        limits: LoanTransferLimits,
    ) -> ObligationStatus {
        let mut depth = 1_usize;
        let mut current = Some(parent);
        let mut seen = BTreeSet::new();
        while let Some(id) = current {
            if !seen.insert(id) {
                depth = usize::MAX;
                break;
            }
            current = self.state.loan(id).and_then(|loan| loan.parent());
            if current.is_some() {
                depth = depth.saturating_add(1);
            }
        }
        let status = if depth <= limits.max_reborrow_depth {
            ObligationStatus::Proven
        } else {
            self.state
                .mark_loan_precision_loss(LoanPrecisionLoss::ReborrowDepthBudget);
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::LoanReborrowDepthWithinBudget {
                loan,
                limit: limits.max_reborrow_depth,
            },
            status,
        );
        status
    }

    fn restore_parent_after_child(&mut self, child: VirLoanId, parent: Option<VirLoanId>) {
        let Some(parent_id) = parent else { return };
        let child_status = no_active_child_status(&self.state, parent_id);
        if let Some(parent) = self.state.loan_mut(parent_id) {
            parent.set_activity(match (parent.activity(), child_status) {
                // A shared parent remains usable while shared children are
                // live, so ending one child must not destroy that fact (and
                // need not wait for sibling children to end).
                (LoanActivity::Active, _) => LoanActivity::Active,
                (LoanActivity::Suspended, ObligationStatus::Proven) => LoanActivity::Active,
                (LoanActivity::Suspended, _) => LoanActivity::Suspended,
                _ => LoanActivity::MaybeActive,
            });
        }
        debug_assert!(
            self.state
                .loan(child)
                .is_some_and(|loan| loan.activity() == LoanActivity::Ended)
        );
    }

    fn check(&mut self, condition_id: VirValueId) -> Result<(), TransferError> {
        let condition = bool_fact(&self.state, condition_id)?;
        let status = if matches!(condition, AbstractBool::True)
            || self
                .state
                .path_condition()
                .implies(PathFact::boolean(condition_id, true))
        {
            ObligationStatus::Proven
        } else if matches!(condition, AbstractBool::False)
            || self
                .state
                .path_condition()
                .implies(PathFact::boolean(condition_id, false))
        {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::CheckTrue {
                condition: condition_id,
            },
            status,
        );
        // Like every fallible instruction, transfer describes the successful
        // continuation under its emitted obligation. The obligation remains
        // unresolved when the condition is unknown, so this refinement cannot
        // by itself make the enclosing sequence verified.
        self.state
            .conjoin_path_fact(PathFact::boolean(condition_id, true));
        Ok(())
    }
}

fn active_object_mask(object: &ObjectAccessFacts) -> ActiveObjectMask {
    let mut grouped = BTreeMap::<
        (Vec<VirObjectPathSegment>, VirMemoryAccess, u64, u64),
        BTreeSet<VirVariantId>,
    >::new();
    for variant in object.shape.variants() {
        grouped
            .entry((
                variant.path().segments().to_vec(),
                variant.enum_access(),
                variant.tag().start_bytes(),
                variant.tag().end_bytes(),
            ))
            .or_default()
            .insert(variant.variant());
    }
    let mut enum_sites = grouped
        .into_iter()
        .map(|((path, access, start, end), variants)| EnumSite {
            path,
            access,
            offset_bytes: start,
            tag: ByteRange::new(start, end).expect("canonical enum tag range"),
            variants,
        })
        .collect::<Vec<_>>();
    enum_sites.sort_by(|left, right| {
        left.path
            .len()
            .cmp(&right.path.len())
            .then_with(|| left.path.cmp(&right.path))
            .then_with(|| left.access.cmp(&right.access))
    });

    let mut choices = BTreeMap::<Vec<VirObjectPathSegment>, ActiveVariantState>::new();
    let mut sites = Vec::new();
    for site in enum_sites {
        if !object_path_possible(&site.path, &choices) {
            continue;
        }
        let state = object
            .pointer
            .offset_bytes()
            .exact_value()
            .and_then(|base| base.checked_add(site.offset_bytes))
            .zip(object.allocation.as_ref())
            .map_or(ActiveVariantState::Unknown, |(offset, allocation)| {
                allocation.active_variant(ObjectStateKey::new(offset, site.access))
            });
        let status = active_variant_status(&state, &site.variants);
        choices.insert(site.path.clone(), state.clone());
        sites.push((site, state, status));
    }

    let mut possible_value_bytes = ByteSet::new();
    let mut guaranteed_value_bytes = ByteSet::new();
    for leaf in object.shape.leaves() {
        let Ok(range) = object_relative_range(leaf.bytes()) else {
            continue;
        };
        if object_path_possible(leaf.path().segments(), &choices) {
            possible_value_bytes.insert(range);
        }
        if object_path_guaranteed(leaf.path().segments(), &choices) {
            guaranteed_value_bytes.insert(range);
        }
    }
    let possible_resource_leaves = object
        .shape
        .resource_leaves()
        .iter()
        .filter(|leaf| object_path_possible(leaf.path().segments(), &choices))
        .cloned()
        .collect();
    let guaranteed_resource_leaves = object
        .shape
        .resource_leaves()
        .iter()
        .filter(|leaf| object_path_guaranteed(leaf.path().segments(), &choices))
        .cloned()
        .collect();
    for (site, _, _) in &sites {
        let tag = site.tag;
        if object_path_possible(&site.path, &choices) {
            possible_value_bytes.insert(tag);
        }
        if object_path_guaranteed(&site.path, &choices) {
            guaranteed_value_bytes.insert(tag);
        }
    }

    ActiveObjectMask {
        possible_value_bytes,
        guaranteed_value_bytes,
        possible_resource_leaves,
        guaranteed_resource_leaves,
        sites,
    }
}

fn object_path_possible(
    path: &[VirObjectPathSegment],
    choices: &BTreeMap<Vec<VirObjectPathSegment>, ActiveVariantState>,
) -> bool {
    let mut prefix = Vec::new();
    for segment in path {
        if let VirObjectPathSegment::Variant(variant) = segment {
            match choices.get(&prefix).unwrap_or(&ActiveVariantState::Unknown) {
                ActiveVariantState::Exact(active) if active != variant => return false,
                ActiveVariantState::Alternatives(active) if !active.contains(variant) => {
                    return false;
                }
                ActiveVariantState::Exact(_)
                | ActiveVariantState::Alternatives(_)
                | ActiveVariantState::Unknown => {}
            }
        }
        prefix.push(*segment);
    }
    true
}

fn object_path_guaranteed(
    path: &[VirObjectPathSegment],
    choices: &BTreeMap<Vec<VirObjectPathSegment>, ActiveVariantState>,
) -> bool {
    let mut prefix = Vec::new();
    for segment in path {
        if let VirObjectPathSegment::Variant(variant) = segment {
            match choices.get(&prefix) {
                Some(ActiveVariantState::Exact(active)) if active == variant => {}
                _ => return false,
            }
        }
        prefix.push(*segment);
    }
    true
}

fn active_variant_status(
    state: &ActiveVariantState,
    declared: &BTreeSet<VirVariantId>,
) -> ObligationStatus {
    let Some(active) = state.alternatives() else {
        return ObligationStatus::Unknown;
    };
    if active.is_empty() || !active.is_subset(declared) {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Proven
    }
}

fn active_variant_allows_access(
    active: &ActiveVariantState,
    allowed: &BTreeSet<VirVariantId>,
) -> ObligationStatus {
    let Some(active) = active.alternatives() else {
        return ObligationStatus::Unknown;
    };
    if active.is_subset(allowed) {
        ObligationStatus::Proven
    } else if active.is_disjoint(allowed) {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

fn object_relative_range(range: VirObjectByteRange) -> Result<ByteRange, TransferError> {
    ByteRange::new(range.start_bytes(), range.end_bytes())
        .map_err(|_| TransferError::InvalidDerivedRange)
}

fn prepare_repeated_object_state(
    allocation: &mut AbstractAllocation,
    shape: &VirObjectShape,
) -> Result<(), TransferError> {
    let object_bytes = shape.size_bytes();
    if object_bytes == 0 || !allocation.size_bytes().is_multiple_of(object_bytes) {
        return Ok(());
    }
    let count = allocation.size_bytes() / object_bytes;
    let enum_sites = shape
        .variants()
        .iter()
        .map(|variant| (variant.tag().start_bytes(), variant.enum_access()))
        .collect::<BTreeSet<_>>();
    for index in 0..count {
        let Some(base) = index.checked_mul(object_bytes) else {
            break;
        };
        for padding in shape.padding() {
            let Some(start) = base.checked_add(padding.start_bytes()) else {
                continue;
            };
            let Some(end) = base.checked_add(padding.end_bytes()) else {
                continue;
            };
            allocation.forget_initialization(
                ByteRange::new(start, end).map_err(|_| TransferError::InvalidDerivedRange)?,
            )?;
        }
        for (offset, access) in &enum_sites {
            let Some(offset) = base.checked_add(*offset) else {
                continue;
            };
            let _ = allocation.set_active_variant(
                ObjectStateKey::new(offset, *access),
                ActiveVariantState::Unknown,
            )?;
        }
    }
    Ok(())
}

fn object_ranges_status(
    pointer: AbstractPointer,
    relative_ranges: &ByteSet,
    mut status: impl FnMut(ByteRange) -> ObligationStatus,
) -> ObligationStatus {
    let mut result = ObligationStatus::Proven;
    for relative in relative_ranges.ranges() {
        let Some(range) = relative_access_envelope(pointer.offset_bytes(), *relative) else {
            return ObligationStatus::Unknown;
        };
        result = combine_pair(result, status(range));
        if result == ObligationStatus::Refuted {
            return result;
        }
    }
    if relative_ranges.is_precise() {
        result
    } else {
        combine_pair(result, ObligationStatus::Unknown)
    }
}

fn relative_access_envelope(offset: U64Interval, relative: ByteRange) -> Option<ByteRange> {
    ByteRange::new(
        offset.lower().checked_add(relative.start())?,
        offset.upper().checked_add(relative.end())?,
    )
    .ok()
}

fn relative_definite_access(offset: U64Interval, relative: ByteRange) -> Option<ByteRange> {
    let start = offset.upper().checked_add(relative.start())?;
    let end = offset.lower().checked_add(relative.end())?;
    (start < end)
        .then(|| ByteRange::new(start, end).ok())
        .flatten()
}

fn copyable_object_status(memory: &VirMemorySchema, access: VirMemoryAccess) -> ObligationStatus {
    let supported = memory
        .type_capabilities(access.ty)
        .is_some_and(|capability| {
            capability.value == crate::ValueCapability::Copy
                && capability.size == crate::SizeCapability::Sized
        })
        && memory.object_shape(access).is_ok_and(|shape| {
            shape.resource_leaves().iter().all(|leaf| {
                leaf.kind() == VirPointerKind::Reference
                    && leaf.mutability() == VirMutability::Const
            })
        });
    if supported {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Refuted
    }
}

fn movable_object_status(memory: &VirMemorySchema, shape: &VirObjectShape) -> ObligationStatus {
    if memory
        .type_capabilities(shape.access().ty)
        .is_none_or(|capability| capability.size != crate::SizeCapability::Sized)
        || shape
            .resource_leaves()
            .iter()
            .any(|leaf| leaf.kind() == VirPointerKind::Raw)
    {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Proven
    }
}

fn droppable_object_status(memory: &VirMemorySchema, access: VirMemoryAccess) -> ObligationStatus {
    if memory
        .type_capabilities(access.ty)
        .is_some_and(|capability| {
            capability.drop == crate::DropCapability::TrivialDrop
                && !capability.contains_resource
                && capability.size == crate::SizeCapability::Sized
        })
    {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Refuted
    }
}

fn builtin_droppable_object_status(
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
) -> ObligationStatus {
    let supported = memory
        .type_capabilities(access.ty)
        .is_some_and(|capability| {
            matches!(
                capability.drop,
                crate::DropCapability::TrivialDrop | crate::DropCapability::BuiltinDrop
            ) && capability.size == crate::SizeCapability::Sized
        })
        && memory.object_shape(access).is_ok_and(|shape| {
            !shape.resource_leaves().is_empty()
                && shape
                    .resource_leaves()
                    .iter()
                    .all(|leaf| leaf.kind() != VirPointerKind::Raw)
        });
    if supported {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Refuted
    }
}

pub(super) fn object_drop_payload_status(
    state: &ResourceState,
    payload: &TypedResourcePayload,
) -> ObligationStatus {
    let pointer = payload.pointer();
    let permission = payload.permission();
    let AbstractProvenance::Known(allocation_id) = pointer.provenance() else {
        return ObligationStatus::Unknown;
    };
    let Some(allocation) = state.allocation(allocation_id) else {
        return ObligationStatus::Unknown;
    };
    combine_statuses([
        base_pointer_status(pointer.offset_bytes()),
        permission_availability_status(permission.availability()),
        free_capability_status(permission.free_capability()),
        provenance_match_status(permission.provenance(), allocation_id),
        liveness_status(allocation.liveness()),
        ownership_status(allocation.ownership()),
        full_permission_status(permission.range(), allocation.size_bytes()),
        allocation_resource_payload_empty_status(allocation),
    ])
}

fn owned_resource_pointee(
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
) -> Result<VirMemoryAccess, TransferError> {
    let Some(VirMemoryTypeKind::Pointer {
        pointee,
        kind: VirPointerKind::Own,
        ..
    }) = memory.kind(access.ty)
    else {
        return Err(TransferError::InvalidValidatedMemoryAccess(access));
    };
    memory
        .access(*pointee)
        .ok_or(TransferError::InvalidValidatedMemoryAccess(access))
}

#[derive(Clone, Copy)]
enum StorableResource {
    Own {
        pointee: VirMemoryAccess,
    },
    Reference {
        pointee: VirMemoryAccess,
        kind: VirLoanKind,
    },
}

impl StorableResource {
    const fn pointee(self) -> VirMemoryAccess {
        match self {
            Self::Own { pointee } | Self::Reference { pointee, .. } => pointee,
        }
    }
}

fn storable_resource(
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
) -> Result<StorableResource, TransferError> {
    let Some(VirMemoryTypeKind::Pointer {
        pointee,
        kind,
        mutability,
    }) = memory.kind(access.ty)
    else {
        return Err(TransferError::InvalidValidatedMemoryAccess(access));
    };
    let pointee = memory
        .access(*pointee)
        .ok_or(TransferError::InvalidValidatedMemoryAccess(access))?;
    match kind {
        VirPointerKind::Own => Ok(StorableResource::Own { pointee }),
        VirPointerKind::Reference => Ok(StorableResource::Reference {
            pointee,
            kind: if *mutability == crate::VirMutability::Mutable {
                VirLoanKind::Mutable
            } else {
                VirLoanKind::Shared
            },
        }),
        VirPointerKind::Raw => Err(TransferError::InvalidValidatedMemoryAccess(access)),
    }
}

fn reference_pointee(
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
) -> Result<VirMemoryAccess, TransferError> {
    if let Some(VirMemoryTypeKind::Slice { element, .. }) = memory.kind(access.ty) {
        return memory
            .access(*element)
            .ok_or(TransferError::InvalidValidatedMemoryAccess(access));
    }
    match storable_resource(memory, access)? {
        StorableResource::Reference { pointee, .. } => Ok(pointee),
        StorableResource::Own { .. } => Err(TransferError::InvalidValidatedMemoryAccess(access)),
    }
}

fn pointer_access_range(
    memory: &VirMemorySchema,
    pointer: AbstractPointer,
    access: VirMemoryAccess,
) -> Option<ByteRange> {
    let width = memory.layout(access.layout)?.size_bytes;
    access_envelope(pointer.offset_bytes(), width)
}

fn stored_loan_authority_status(
    loan: &AbstractLoan,
    allocation: AbstractAllocationId,
    payload: ResourcePayloadKey,
    expected: VirLoanId,
    expected_kind: VirLoanKind,
) -> ObligationStatus {
    combine_statuses([
        if loan
            .authorities()
            .contains(&super::resource::AbstractLoanAuthority::stored(
                allocation, payload,
            ))
        {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Refuted
        },
        if loan.kind() == expected_kind {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Refuted
        },
        loan_authority_status(PermissionAuthority::Loan(expected), expected),
    ])
}

fn loan_authority_access_status_for_payload(
    loan: &AbstractLoan,
    pointer: AbstractPointer,
    width: Option<u64>,
    required: AccessPermission,
) -> ObligationStatus {
    let Some(width) = width else {
        return ObligationStatus::Unknown;
    };
    let capability = match (loan.kind(), required) {
        (VirLoanKind::Shared, AccessPermission::Read)
        | (VirLoanKind::Mutable, AccessPermission::Read | AccessPermission::Write) => {
            ObligationStatus::Proven
        }
        (VirLoanKind::Shared, AccessPermission::Write) => ObligationStatus::Refuted,
        (_, AccessPermission::MaybeWrite) => ObligationStatus::Unknown,
    };
    let range = permission_coverage_status(loan.actual_range(), pointer, width);
    combine_statuses([
        provenance_equal_status(loan.provenance(), pointer.provenance()),
        range,
        capability,
    ])
}

const fn move_path_availability_status(state: &MovePathState) -> ObligationStatus {
    match state {
        MovePathState::Available(_) => ObligationStatus::Proven,
        MovePathState::Moved => ObligationStatus::Refuted,
        MovePathState::Unknown => ObligationStatus::Unknown,
    }
}

fn object_resource_payload_empty_status(
    object: &ObjectAccessFacts,
    memory: &VirMemorySchema,
) -> ObligationStatus {
    let (Some(allocation), Some(base)) = (
        &object.allocation,
        object.pointer.offset_bytes().exact_value(),
    ) else {
        return ObligationStatus::Unknown;
    };
    let Some(end) = base.checked_add(object.shape.size_bytes()) else {
        return ObligationStatus::Unknown;
    };
    let mut status = if allocation.object_state().is_precise() {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Unknown
    };
    // Check the entire target storage range, not just the new variant's mask.
    // Other fields in the same allocation retain their independent authority.
    for (key, state) in allocation.object_state().resource_payloads() {
        let Some(layout) = memory.layout(key.access().layout) else {
            return ObligationStatus::Unknown;
        };
        if key.offset_bytes() >= end || key.offset_bytes().saturating_add(layout.size_bytes) <= base
        {
            continue;
        }
        match state {
            MovePathState::Available(_) => return ObligationStatus::Refuted,
            MovePathState::Unknown => status = ObligationStatus::Unknown,
            MovePathState::Moved => {}
        }
    }
    status
}

fn empty_tagged_storage(object: &ObjectAccessFacts, memory: &VirMemorySchema) -> Option<ByteSet> {
    // Only builtin heap allocation establishes the physical empty tagged
    // representation in every consumer. Fresh tagged LocalStorage does not.
    if !matches!(
        object.allocation_id,
        Some(AbstractAllocationId::VirAllocationSite(_))
    ) {
        return None;
    }
    // Unlike normal active cleanup, empty storage must have no representation
    // bytes in any variant, including currently inactive payload ranges.
    let mut bytes = ByteSet::new();
    for range in object.shape.value_bytes() {
        bytes.insert(object_relative_range(*range).ok()?);
    }
    let empty = object.allocation.as_ref().is_some_and(|allocation| {
        object_ranges_status(object.pointer, &bytes, |range| {
            initialization_status(
                allocation.initialization().classify(range),
                InitializationRequirement::Uninitialized,
            )
        })
        .is_proven()
    }) && object_resource_payload_empty_status(object, memory).is_proven();
    empty.then_some(bytes)
}

fn empty_resource_paths(allocation: &AbstractAllocation) -> Vec<ResourcePayloadKey> {
    allocation
        .object_state()
        .resource_payloads()
        .iter()
        .filter_map(|(key, state)| (*state == MovePathState::Moved).then_some(*key))
        .collect()
}

/// Only for object effects that explicitly manage payload transfer/retirement.
/// Arbitrary writes and calls must continue to forget resource authority.
fn restore_empty_resource_paths(
    allocation: &mut AbstractAllocation,
    keys: &[ResourcePayloadKey],
) -> Result<(), TransferError> {
    for key in keys {
        if allocation.resource_payload(*key) == MovePathState::Unknown {
            let _ = allocation.set_resource_payload(*key, MovePathState::Moved)?;
        }
    }
    Ok(())
}

fn allocation_resource_payload_empty_status(allocation: &AbstractAllocation) -> ObligationStatus {
    let mut status = if allocation.object_state().is_precise() {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Unknown
    };
    for state in allocation.object_state().resource_payloads().values() {
        match state {
            MovePathState::Available(_) => return ObligationStatus::Refuted,
            MovePathState::Unknown => status = ObligationStatus::Unknown,
            MovePathState::Moved => {}
        }
    }
    status
}

const fn combine_pair(left: ObligationStatus, right: ObligationStatus) -> ObligationStatus {
    match (left, right) {
        (ObligationStatus::Refuted, _) | (_, ObligationStatus::Refuted) => {
            ObligationStatus::Refuted
        }
        (ObligationStatus::Unknown, _) | (_, ObligationStatus::Unknown) => {
            ObligationStatus::Unknown
        }
        (ObligationStatus::Proven, ObligationStatus::Proven) => ObligationStatus::Proven,
    }
}

#[derive(Clone, Copy)]
enum InitializationRequirement {
    None,
    Initialized,
    Uninitialized,
}

#[derive(Clone, Copy)]
enum MemoryEffect {
    None,
    WriteValue,
}

fn scalar_fact(
    memory: &VirMemorySchema,
    state: &ResourceState,
    id: VirValueId,
    access: VirMemoryAccess,
) -> Result<(), TransferError> {
    match memory.kind(access.ty) {
        Some(crate::VirMemoryTypeKind::Bool) => bool_fact(state, id).map(|_| ()),
        Some(crate::VirMemoryTypeKind::Integer(
            crate::VirIntegerType::U64 | crate::VirIntegerType::Usize,
        )) => word_fact(state, id).map(|_| ()),
        _ => Err(TransferError::InvalidValidatedMemoryAccess(access)),
    }
}

fn word_fact(state: &ResourceState, id: VirValueId) -> Result<U64Interval, TransferError> {
    match state.value(id).copied() {
        Some(AbstractValue::U64(value)) => Ok(value),
        Some(AbstractValue::EnumDiscriminant(value)) => Ok(value.interval()),
        None => Ok(U64Interval::unknown()),
        Some(found) => Err(value_type_mismatch(id, VirType::U64, found)),
    }
}

fn word_expression(
    state: &ResourceState,
    id: VirValueId,
    interval: U64Interval,
) -> Option<AffineExpression> {
    // An exact word (notably an empty slice's length) is not another variable
    // term. Normalize it before enforcing the fixed two-root address budget.
    interval
        .exact_value()
        .map(AffineExpression::constant)
        .or_else(|| state.word_expression(id))
        .or_else(|| Some(AffineExpression::identity(id)))
}

fn bool_fact(state: &ResourceState, id: VirValueId) -> Result<AbstractBool, TransferError> {
    match state.value(id).copied() {
        Some(AbstractValue::Bool(value)) => Ok(value),
        None => Ok(AbstractBool::Unknown),
        Some(found) => Err(value_type_mismatch(id, VirType::Bool, found)),
    }
}

fn pointer_fact(state: &ResourceState, id: VirValueId) -> Result<AbstractPointer, TransferError> {
    match state.value(id).copied() {
        Some(AbstractValue::Pointer(value)) => Ok(value),
        None => Ok(unknown_pointer()),
        Some(found) => Err(value_type_mismatch(
            id,
            VirType::Pointer {
                access: VirMemoryAccess::core_u64(),
            },
            found,
        )),
    }
}

fn permission_fact(
    state: &ResourceState,
    id: VirValueId,
) -> Result<AbstractPermission, TransferError> {
    match state.value(id).copied() {
        Some(AbstractValue::Permission(value)) => Ok(value),
        None => Ok(unknown_permission()),
        Some(found) => Err(value_type_mismatch(id, VirType::Permission, found)),
    }
}

fn loan_range(effect: VirLoanEffect) -> Result<ByteRange, TransferError> {
    ByteRange::new(effect.range.start_bytes, effect.range.end_bytes)
        .map_err(|_| TransferError::InvalidValidatedLoan(effect.loan))
}

const fn loan_access(kind: VirLoanKind) -> AccessPermission {
    match kind {
        VirLoanKind::Shared => AccessPermission::Read,
        VirLoanKind::Mutable => AccessPermission::Write,
    }
}

const fn owner_authority_status(authority: PermissionAuthority) -> ObligationStatus {
    match authority {
        PermissionAuthority::Owner => ObligationStatus::Proven,
        PermissionAuthority::Loan(_) => ObligationStatus::Refuted,
        PermissionAuthority::Unknown => ObligationStatus::Unknown,
    }
}

const fn loan_authority_status(
    authority: PermissionAuthority,
    expected: VirLoanId,
) -> ObligationStatus {
    match authority {
        PermissionAuthority::Loan(found) if found.get() == expected.get() => {
            ObligationStatus::Proven
        }
        PermissionAuthority::Owner | PermissionAuthority::Loan(_) => ObligationStatus::Refuted,
        PermissionAuthority::Unknown => ObligationStatus::Unknown,
    }
}

fn tracked_loan_authority_status(
    loan: &AbstractLoan,
    permission: VirValueId,
    authority: PermissionAuthority,
    expected: VirLoanId,
) -> ObligationStatus {
    combine_statuses([
        loan_authority_status(authority, expected),
        if loan.has_value_authority(permission) {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Refuted
        },
    ])
}

const fn loan_activity_access_status(activity: LoanActivity) -> ObligationStatus {
    match activity {
        LoanActivity::Active => ObligationStatus::Proven,
        LoanActivity::Suspended | LoanActivity::Ended => ObligationStatus::Refuted,
        LoanActivity::MaybeActive => ObligationStatus::Unknown,
    }
}

fn pointer_within_range_status(pointer: AbstractPointer, range: ByteRange) -> ObligationStatus {
    let offset = pointer.offset_bytes();
    if range.start() <= offset.lower() && offset.upper() < range.end() {
        return ObligationStatus::Proven;
    }
    if offset.upper() < range.start() || offset.lower() >= range.end() {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

fn pointer_within_slice_range_status(
    pointer: AbstractPointer,
    range: ByteRange,
) -> ObligationStatus {
    // A slice may be empty at any endpoint, including a nonempty envelope's
    // one-past endpoint. Element access has a separate positive-width check.
    let offset = pointer.offset_bytes();
    if range.start() <= offset.lower() && offset.upper() <= range.end() {
        return ObligationStatus::Proven;
    }
    if offset.upper() < range.start() || offset.lower() > range.end() {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

fn provenance_equal_status(
    left: AbstractProvenance,
    right: AbstractProvenance,
) -> ObligationStatus {
    match (left, right) {
        (AbstractProvenance::Known(left), AbstractProvenance::Known(right)) if left == right => {
            ObligationStatus::Proven
        }
        (AbstractProvenance::Known(_), AbstractProvenance::Known(_)) => ObligationStatus::Refuted,
        _ => ObligationStatus::Unknown,
    }
}

fn loan_metadata_status(
    loan: &AbstractLoan,
    effect: VirLoanEffect,
    provenance: AbstractProvenance,
    range: ByteRange,
) -> ObligationStatus {
    let static_metadata = if loan.range() == range
        && loan.kind() == effect.kind
        && loan.region() == effect.region
        && loan.parent() == effect.parent
    {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Refuted
    };
    combine_statuses([
        static_metadata,
        provenance_equal_status(loan.provenance(), provenance),
    ])
}

fn parent_contains_child_status(
    parent: &AbstractLoan,
    effect: VirLoanEffect,
    provenance: AbstractProvenance,
    range: ByteRange,
) -> ObligationStatus {
    let kind = if parent.kind() == VirLoanKind::Mutable || effect.kind == VirLoanKind::Shared {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Refuted
    };
    let range = if parent.range().contains(range) {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Refuted
    };
    combine_statuses([
        kind,
        range,
        provenance_equal_status(parent.provenance(), provenance),
    ])
}

fn no_active_child_status(state: &ResourceState, parent: VirLoanId) -> ObligationStatus {
    let mut status = ObligationStatus::Proven;
    for child in state
        .loans()
        .values()
        .filter(|loan| loan.parent() == Some(parent))
    {
        status = match child.activity() {
            LoanActivity::Ended => status,
            LoanActivity::MaybeActive => combine_statuses([status, ObligationStatus::Unknown]),
            LoanActivity::Active | LoanActivity::Suspended => ObligationStatus::Refuted,
        };
    }
    status
}

fn available_loan_authorities(state: &ResourceState, loan: VirLoanId) -> usize {
    state.loan(loan).map_or(0, |loan| loan.authorities().len())
}

fn loan_creation_compatibility(
    state: &ResourceState,
    effect: VirLoanEffect,
    parent: Option<VirLoanId>,
    footprint: Option<MemoryFootprint>,
    limits: DifferenceLimits,
    pairs: &TransferRelations,
) -> ObligationStatus {
    let Ok(range) = loan_range(effect) else {
        return ObligationStatus::Refuted;
    };
    let provenance = pointer_fact(state, effect.source_pointer)
        .map(AbstractPointer::provenance)
        .unwrap_or(AbstractProvenance::Unknown);
    let mut ignored = BTreeSet::new();
    let mut ancestor = parent;
    while let Some(id) = ancestor {
        if !ignored.insert(id) {
            return ObligationStatus::Unknown;
        }
        ancestor = state.loan(id).and_then(|loan| loan.parent());
    }
    let mut status = ObligationStatus::Proven;
    for (&id, loan) in state.loans() {
        if ignored.contains(&id) || matches!(loan.activity(), LoanActivity::Ended) {
            continue;
        }
        if !pairs.charge() {
            return ObligationStatus::Unknown;
        }
        let overlap = loan_overlap_status(
            state,
            loan,
            provenance,
            range,
            footprint.map_or(AbstractByteRange::Unknown, |f| f.range),
            limits,
            pairs,
        );
        let compatible = match (overlap, loan.activity()) {
            (_, LoanActivity::Active)
                if loan.kind() == VirLoanKind::Shared && effect.kind == VirLoanKind::Shared =>
            {
                ObligationStatus::Proven
            }
            (ObligationStatus::Proven, _) => ObligationStatus::Proven,
            (ObligationStatus::Refuted, LoanActivity::MaybeActive) => ObligationStatus::Unknown,
            (ObligationStatus::Refuted, _)
                if loan.kind() == VirLoanKind::Shared && effect.kind == VirLoanKind::Shared =>
            {
                ObligationStatus::Proven
            }
            (ObligationStatus::Refuted, _) => ObligationStatus::Refuted,
            (ObligationStatus::Unknown, _) => ObligationStatus::Unknown,
        };
        status = combine_statuses([status, compatible]);
    }
    if status.is_proven()
        && state.loan_precision_losses().iter().any(|loss| {
            matches!(
                loss,
                LoanPrecisionLoss::ActiveLoanBudget
                    | LoanPrecisionLoss::LoanJoin
                    | LoanPrecisionLoss::LoanLoopWidening
            )
        })
    {
        ObligationStatus::Unknown
    } else {
        status
    }
}

/// `Proven` means definitely disjoint; `Refuted` means definitely overlapping.
fn loan_overlap_status(
    state: &ResourceState,
    loan: &AbstractLoan,
    provenance: AbstractProvenance,
    range: ByteRange,
    actual: AbstractByteRange,
    limits: DifferenceLimits,
    pairs: &TransferRelations,
) -> ObligationStatus {
    match provenance_equal_status(loan.provenance(), provenance) {
        ObligationStatus::Proven if !loan.range().overlaps(range) => ObligationStatus::Proven,
        ObligationStatus::Proven => pairs.queries.disjoint(
            state,
            loan.provenance(),
            loan.actual_range(),
            provenance,
            actual,
            limits,
        ),
        ObligationStatus::Refuted => ObligationStatus::Proven,
        ObligationStatus::Unknown => ObligationStatus::Unknown,
    }
}

/// Keep the actual selected bytes separate from the conservative envelope at
/// every access consumer. Free uses the whole allocation, never an element.
#[derive(Clone, Copy)]
struct LoanAccess {
    pointer: AbstractPointer,
    envelope: Option<ByteRange>,
    range: AbstractByteRange,
    required: AccessPermission,
}

impl LoanAccess {
    fn bytes(pointer: AbstractPointer, width: u64, required: AccessPermission) -> Self {
        Self {
            pointer,
            envelope: access_envelope(pointer.offset_bytes(), width),
            range: super::relation::range::access_range(pointer, width),
            required,
        }
    }

    fn whole(
        pointer: AbstractPointer,
        range: Option<ByteRange>,
        required: AccessPermission,
    ) -> Self {
        Self {
            pointer,
            envelope: range,
            range: range.map_or(AbstractByteRange::Unknown, AbstractByteRange::Exact),
            required,
        }
    }
}

fn owner_loan_access_status(
    state: &ResourceState,
    access: LoanAccess,
    limits: DifferenceLimits,
    pairs: &TransferRelations,
) -> ObligationStatus {
    let Some(envelope) = access.envelope else {
        return if state.loans().is_empty() && state.loan_precision_losses().is_empty() {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Unknown
        };
    };
    let mut status = ObligationStatus::Proven;
    for loan in state.loans().values() {
        if matches!(loan.activity(), LoanActivity::Ended) {
            continue;
        }
        if !pairs.charge() {
            return ObligationStatus::Unknown;
        }
        let overlap = loan_overlap_status(
            state,
            loan,
            access.pointer.provenance(),
            envelope,
            access.range,
            limits,
            pairs,
        );
        let compatible = match (overlap, loan.activity(), loan.kind(), access.required) {
            (_, LoanActivity::Active, VirLoanKind::Shared, AccessPermission::Read) => {
                ObligationStatus::Proven
            }
            (ObligationStatus::Proven, _, _, _) => ObligationStatus::Proven,
            (ObligationStatus::Unknown, _, _, _) => ObligationStatus::Unknown,
            (ObligationStatus::Refuted, LoanActivity::MaybeActive, _, _) => {
                ObligationStatus::Unknown
            }
            (ObligationStatus::Refuted, _, _, _) => ObligationStatus::Refuted,
        };
        status = combine_statuses([status, compatible]);
    }
    if status.is_proven()
        && state.loan_precision_losses().iter().any(|loss| {
            matches!(
                loss,
                LoanPrecisionLoss::ActiveLoanBudget
                    | LoanPrecisionLoss::LoanJoin
                    | LoanPrecisionLoss::LoanLoopWidening
            )
        })
    {
        ObligationStatus::Unknown
    } else {
        status
    }
}

fn loan_authority_access_status(
    state: &ResourceState,
    loan_id: VirLoanId,
    permission: VirValueId,
    access: LoanAccess,
    limits: DifferenceLimits,
    pairs: &TransferRelations,
) -> ObligationStatus {
    let Some(loan) = state.loan(loan_id) else {
        return ObligationStatus::Unknown;
    };
    let Some(envelope) = access.envelope else {
        return ObligationStatus::Unknown;
    };
    let capability = match (loan.kind(), access.required) {
        (VirLoanKind::Shared, AccessPermission::Read)
        | (VirLoanKind::Mutable, AccessPermission::Read | AccessPermission::Write) => {
            ObligationStatus::Proven
        }
        (VirLoanKind::Shared, AccessPermission::Write) => ObligationStatus::Refuted,
        (_, AccessPermission::MaybeWrite) => ObligationStatus::Unknown,
    };
    let range = if !loan.range().overlaps(envelope) && envelope.length() > 0 {
        ObligationStatus::Refuted
    } else if matches!(loan.actual_range(), AbstractByteRange::Exact(actual) if actual.contains(envelope))
    {
        // Every possible selected access lies in an actual exact authority.
        // An envelope may prove containment, never refute a symbolic selection.
        ObligationStatus::Proven
    } else {
        pairs
            .queries
            .contained(state, loan.actual_range(), access.range, limits)
    };
    combine_statuses([
        if loan.has_value_authority(permission) {
            ObligationStatus::Proven
        } else {
            ObligationStatus::Refuted
        },
        loan_activity_access_status(loan.activity()),
        provenance_equal_status(loan.provenance(), access.pointer.provenance()),
        range,
        capability,
    ])
}

fn permission_loan_access_status(
    state: &ResourceState,
    permission_id: VirValueId,
    permission: AbstractPermission,
    access: LoanAccess,
    limits: DifferenceLimits,
    pairs: &TransferRelations,
) -> (Option<VirLoanId>, ObligationStatus) {
    match permission.authority() {
        PermissionAuthority::Owner => {
            (None, owner_loan_access_status(state, access, limits, pairs))
        }
        PermissionAuthority::Loan(loan) => (
            Some(loan),
            loan_authority_access_status(state, loan, permission_id, access, limits, pairs),
        ),
        PermissionAuthority::Unknown => (None, ObligationStatus::Unknown),
    }
}

fn ensure_fact_type(
    state: &ResourceState,
    id: VirValueId,
    expected: VirType,
) -> Result<(), TransferError> {
    let Some(found) = state.value(id).copied() else {
        return Ok(());
    };
    if abstract_value_matches_type(found, expected) {
        Ok(())
    } else {
        Err(TransferError::AbstractValueTypeMismatch {
            value: id,
            expected,
            found: abstract_value_type_or(found, expected),
        })
    }
}

fn value_type_mismatch(
    value: VirValueId,
    expected: VirType,
    found: AbstractValue,
) -> TransferError {
    TransferError::AbstractValueTypeMismatch {
        value,
        expected,
        found: abstract_value_type(found),
    }
}

pub(super) const fn abstract_value_type(value: AbstractValue) -> VirType {
    match value {
        AbstractValue::U64(_) | AbstractValue::EnumDiscriminant(_) => VirType::U64,
        AbstractValue::Bool(_) => VirType::Bool,
        AbstractValue::Pointer(pointer) => VirType::Pointer {
            access: match pointer.memory_access() {
                Some(access) => access,
                None => VirMemoryAccess::core_u64(),
            },
        },
        AbstractValue::Permission(_) => VirType::Permission,
    }
}

pub(super) fn unknown_value(ty: VirType) -> AbstractValue {
    match ty {
        VirType::U64 => AbstractValue::U64(U64Interval::unknown()),
        VirType::Bool => AbstractValue::Bool(AbstractBool::Unknown),
        VirType::Pointer { access } => {
            AbstractValue::Pointer(unknown_pointer().with_memory_access(Some(access)))
        }
        VirType::Permission => AbstractValue::Permission(fresh_unknown_permission()),
    }
}

pub(super) fn abstract_value_matches_type(value: AbstractValue, expected: VirType) -> bool {
    match (value, expected) {
        (AbstractValue::U64(_) | AbstractValue::EnumDiscriminant(_), VirType::U64)
        | (AbstractValue::Bool(_), VirType::Bool)
        | (AbstractValue::Permission(_), VirType::Permission) => true,
        (AbstractValue::Pointer(pointer), VirType::Pointer { access }) => {
            match pointer.memory_access() {
                Some(found) => found.ty == access.ty && found.layout == access.layout,
                None => true,
            }
        }
        _ => false,
    }
}

const fn abstract_value_type_or(value: AbstractValue, expected: VirType) -> VirType {
    match (value, expected) {
        (AbstractValue::Pointer(pointer), VirType::Pointer { access }) => VirType::Pointer {
            access: match pointer.memory_access() {
                Some(found) => found,
                None => access,
            },
        },
        (value, _) => abstract_value_type(value),
    }
}

fn unknown_pointer() -> AbstractPointer {
    AbstractPointer::new(
        AbstractProvenance::Unknown,
        U64Interval::unknown(),
        GuaranteedAlignment::one(),
    )
}

pub(super) fn unknown_permission() -> AbstractPermission {
    fresh_unknown_permission().with_availability(PermissionAvailability::MaybeConsumed)
}

fn fresh_unknown_permission() -> AbstractPermission {
    AbstractPermission::new(
        AbstractProvenance::Unknown,
        AbstractByteRange::Unknown,
        AccessPermission::MaybeWrite,
        FreeCapability::Maybe,
    )
    .with_authority(PermissionAuthority::Unknown)
}

fn mark_permission_consumed(
    state: &mut ResourceState,
    id: VirValueId,
) -> Result<(), TransferError> {
    match state.value_mut(id) {
        Some(AbstractValue::Permission(permission)) => {
            permission.mark_consumed();
            Ok(())
        }
        None => Ok(()),
        Some(found) => Err(TransferError::AbstractValueTypeMismatch {
            value: id,
            expected: VirType::Permission,
            found: abstract_value_type(*found),
        }),
    }
}

fn add_word_intervals(left: U64Interval, right: U64Interval) -> U64Interval {
    if let (Some(left), Some(right)) = (left.exact_value(), right.exact_value()) {
        return U64Interval::exact(crate::VIR_SYSTEM_SEMANTICS_V1.word_add(left, right));
    }
    match (
        left.lower().checked_add(right.lower()),
        left.upper().checked_add(right.upper()),
    ) {
        (Some(lower), Some(upper)) => {
            U64Interval::new(lower, upper).unwrap_or_else(|_| U64Interval::unknown())
        }
        _ => U64Interval::unknown(),
    }
}

const fn compare_same_value(predicate: VirIntegerPredicate) -> AbstractBool {
    match predicate {
        VirIntegerPredicate::Equal
        | VirIntegerPredicate::LessOrEqual
        | VirIntegerPredicate::GreaterOrEqual => AbstractBool::True,
        VirIntegerPredicate::NotEqual
        | VirIntegerPredicate::LessThan
        | VirIntegerPredicate::GreaterThan => AbstractBool::False,
    }
}

fn compare_intervals(
    predicate: VirIntegerPredicate,
    left: U64Interval,
    right: U64Interval,
) -> AbstractBool {
    use AbstractBool::{False, True, Unknown};
    match predicate {
        VirIntegerPredicate::Equal => {
            if left.exact_value().is_some() && left == right {
                True
            } else if left.intersection(right).is_none() {
                False
            } else {
                Unknown
            }
        }
        VirIntegerPredicate::NotEqual => {
            match compare_intervals(VirIntegerPredicate::Equal, left, right) {
                True => False,
                False => True,
                Unknown => Unknown,
            }
        }
        VirIntegerPredicate::LessThan => {
            relation_status(left.upper() < right.lower(), left.lower() >= right.upper())
        }
        VirIntegerPredicate::LessOrEqual => {
            relation_status(left.upper() <= right.lower(), left.lower() > right.upper())
        }
        VirIntegerPredicate::GreaterThan => {
            compare_intervals(VirIntegerPredicate::LessThan, right, left)
        }
        VirIntegerPredicate::GreaterOrEqual => {
            compare_intervals(VirIntegerPredicate::LessOrEqual, right, left)
        }
    }
}

const fn relation_status(always_true: bool, always_false: bool) -> AbstractBool {
    if always_true {
        AbstractBool::True
    } else if always_false {
        AbstractBool::False
    } else {
        AbstractBool::Unknown
    }
}

fn access_envelope(offset: U64Interval, width: u64) -> Option<ByteRange> {
    ByteRange::new(offset.lower(), offset.upper().checked_add(width)?).ok()
}

fn definite_write_range(offset: U64Interval, width: u64) -> Option<ByteRange> {
    let end = offset.lower().checked_add(width)?;
    (offset.upper() < end)
        .then(|| ByteRange::new(offset.upper(), end).ok())
        .flatten()
}

const fn known_provenance_status(provenance: AbstractProvenance) -> ObligationStatus {
    match provenance {
        AbstractProvenance::Known(_) => ObligationStatus::Proven,
        AbstractProvenance::Unknown => ObligationStatus::Unknown,
    }
}

const fn memory_access_status(
    found: Option<VirMemoryAccess>,
    expected: VirMemoryAccess,
) -> ObligationStatus {
    match found {
        Some(found)
            if found.ty.get() == expected.ty.get()
                && found.layout.get() == expected.layout.get() =>
        {
            ObligationStatus::Proven
        }
        Some(_) => ObligationStatus::Refuted,
        None => ObligationStatus::Unknown,
    }
}

const fn liveness_status(liveness: LivenessState) -> ObligationStatus {
    match liveness {
        LivenessState::Live => ObligationStatus::Proven,
        LivenessState::Dead => ObligationStatus::Refuted,
        LivenessState::MaybeLive => ObligationStatus::Unknown,
    }
}

const fn ownership_status(ownership: OwnershipState) -> ObligationStatus {
    match ownership {
        OwnershipState::Owned => ObligationStatus::Proven,
        OwnershipState::Unowned => ObligationStatus::Refuted,
        OwnershipState::MaybeOwned => ObligationStatus::Unknown,
    }
}

pub(super) const fn permission_availability_status(
    availability: PermissionAvailability,
) -> ObligationStatus {
    match availability {
        PermissionAvailability::Available => ObligationStatus::Proven,
        PermissionAvailability::Consumed => ObligationStatus::Refuted,
        PermissionAvailability::MaybeConsumed => ObligationStatus::Unknown,
    }
}

const fn permission_writable_status(access: AccessPermission) -> ObligationStatus {
    match access {
        AccessPermission::Write => ObligationStatus::Proven,
        AccessPermission::Read => ObligationStatus::Refuted,
        AccessPermission::MaybeWrite => ObligationStatus::Unknown,
    }
}

const fn free_capability_status(capability: FreeCapability) -> ObligationStatus {
    match capability {
        FreeCapability::Yes => ObligationStatus::Proven,
        FreeCapability::No => ObligationStatus::Refuted,
        FreeCapability::Maybe => ObligationStatus::Unknown,
    }
}

fn provenance_match_status(
    provenance: AbstractProvenance,
    allocation: AbstractAllocationId,
) -> ObligationStatus {
    match provenance {
        AbstractProvenance::Known(found) if found == allocation => ObligationStatus::Proven,
        AbstractProvenance::Known(_) => ObligationStatus::Refuted,
        AbstractProvenance::Unknown => ObligationStatus::Unknown,
    }
}

fn initialization_status(
    class: InitializationClass,
    requirement: InitializationRequirement,
) -> ObligationStatus {
    match (class, requirement) {
        (_, InitializationRequirement::None) => ObligationStatus::Proven,
        (InitializationClass::Initialized, InitializationRequirement::Initialized)
        | (InitializationClass::Uninitialized, InitializationRequirement::Uninitialized) => {
            ObligationStatus::Proven
        }
        (InitializationClass::Initialized, InitializationRequirement::Uninitialized)
        | (InitializationClass::Uninitialized, InitializationRequirement::Initialized) => {
            ObligationStatus::Refuted
        }
        (InitializationClass::MaybeInitialized, _) => ObligationStatus::Unknown,
    }
}

fn abstract_range_from_offsets(
    start: U64Interval,
    start_expression: Option<AffineExpression>,
    end: U64Interval,
    end_expression: Option<AffineExpression>,
) -> AbstractByteRange {
    match (
        symbolic_bound(start, start_expression),
        symbolic_bound(end, end_expression),
    ) {
        (Some(start), Some(end)) => AbstractByteRange::from_bounds(start, end),
        _ => AbstractByteRange::Unknown,
    }
}

const fn exact_abstract_range(range: AbstractByteRange) -> Option<ByteRange> {
    match range {
        AbstractByteRange::Exact(range) => Some(range),
        AbstractByteRange::Symbolic { .. } | AbstractByteRange::Unknown => None,
    }
}

fn subtract_intervals(end: U64Interval, start: U64Interval) -> U64Interval {
    let lower = end.lower().saturating_sub(start.upper());
    let upper = end.upper().saturating_sub(start.lower());
    U64Interval::new(lower.min(upper), upper).unwrap_or_else(|_| U64Interval::unknown())
}

fn base_pointer_status(offset: U64Interval) -> ObligationStatus {
    if offset == U64Interval::exact(0) {
        ObligationStatus::Proven
    } else if !offset.contains(0) {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

fn full_permission_status(range: AbstractByteRange, size_bytes: u64) -> ObligationStatus {
    match range {
        AbstractByteRange::Exact(range) => {
            if range.start() == 0 && range.end() == size_bytes {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Refuted
            }
        }
        AbstractByteRange::Symbolic { start, end }
            if start == SymbolicRangeBound::constant(0)
                && end == SymbolicRangeBound::constant(size_bytes) =>
        {
            ObligationStatus::Proven
        }
        AbstractByteRange::Symbolic { .. } | AbstractByteRange::Unknown => {
            ObligationStatus::Unknown
        }
    }
}

fn split_status(
    range: AbstractByteRange,
    split_at: U64Interval,
    expression: Option<AffineExpression>,
) -> ObligationStatus {
    let Some((start, end)) = range.bounds() else {
        return ObligationStatus::Unknown;
    };
    let Some(split) = symbolic_bound(split_at, expression) else {
        return combine_statuses([
            interval_le_status(start.interval(), split_at),
            interval_le_status(split_at, end.interval()),
        ]);
    };
    combine_statuses([bound_le_status(start, split), bound_le_status(split, end)])
}

fn split_ranges(
    range: AbstractByteRange,
    split_at: U64Interval,
    expression: Option<AffineExpression>,
) -> Result<(AbstractByteRange, AbstractByteRange), TransferError> {
    let Some((start, end)) = range.bounds() else {
        return Ok((AbstractByteRange::Unknown, AbstractByteRange::Unknown));
    };
    let Some(split) = symbolic_bound(split_at, expression) else {
        return Ok((AbstractByteRange::Unknown, AbstractByteRange::Unknown));
    };
    Ok((
        AbstractByteRange::from_bounds(start, split),
        AbstractByteRange::from_bounds(split, end),
    ))
}

fn permission_join_status(
    left: AbstractPermission,
    right: AbstractPermission,
) -> Result<(ObligationStatus, AbstractByteRange), TransferError> {
    let provenance = match (left.provenance(), right.provenance()) {
        (AbstractProvenance::Known(left), AbstractProvenance::Known(right)) if left == right => {
            ObligationStatus::Proven
        }
        (AbstractProvenance::Known(_), AbstractProvenance::Known(_)) => ObligationStatus::Refuted,
        _ => ObligationStatus::Unknown,
    };
    let access = match (left.access(), right.access()) {
        (AccessPermission::Read, AccessPermission::Read)
        | (AccessPermission::Write, AccessPermission::Write) => ObligationStatus::Proven,
        (AccessPermission::Read, AccessPermission::Write)
        | (AccessPermission::Write, AccessPermission::Read) => ObligationStatus::Refuted,
        (AccessPermission::MaybeWrite, _) | (_, AccessPermission::MaybeWrite) => {
            ObligationStatus::Unknown
        }
    };
    let free = match (left.free_capability(), right.free_capability()) {
        (FreeCapability::Yes, FreeCapability::Yes) | (FreeCapability::No, FreeCapability::No) => {
            ObligationStatus::Proven
        }
        (FreeCapability::Maybe, _) | (_, FreeCapability::Maybe) => ObligationStatus::Unknown,
        _ => ObligationStatus::Refuted,
    };
    let authority = match (left.authority(), right.authority()) {
        (PermissionAuthority::Owner, PermissionAuthority::Owner) => ObligationStatus::Proven,
        (PermissionAuthority::Unknown, _) | (_, PermissionAuthority::Unknown) => {
            ObligationStatus::Unknown
        }
        (PermissionAuthority::Loan(_), _) | (_, PermissionAuthority::Loan(_)) => {
            ObligationStatus::Refuted
        }
    };
    let (range_status, joined) = join_permission_ranges(left.range(), right.range());

    let statuses = [provenance, access, free, authority, range_status];
    let compatibility = if statuses.contains(&ObligationStatus::Refuted) {
        ObligationStatus::Refuted
    } else if statuses.iter().all(|status| status.is_proven()) {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Unknown
    };
    Ok((compatibility, joined))
}

fn bound_equal_status(left: SymbolicRangeBound, right: SymbolicRangeBound) -> ObligationStatus {
    if left.expression() == right.expression() {
        ObligationStatus::Proven
    } else if left.interval().intersection(right.interval()).is_none() {
        ObligationStatus::Refuted
    } else {
        ObligationStatus::Unknown
    }
}

fn join_permission_ranges(
    left: AbstractByteRange,
    right: AbstractByteRange,
) -> (ObligationStatus, AbstractByteRange) {
    let (Some((left_start, left_end)), Some((right_start, right_end))) =
        (left.bounds(), right.bounds())
    else {
        return (ObligationStatus::Unknown, AbstractByteRange::Unknown);
    };
    let left_then_right = bound_equal_status(left_end, right_start);
    let right_then_left = bound_equal_status(right_end, left_start);
    if left_then_right.is_proven() {
        (
            ObligationStatus::Proven,
            AbstractByteRange::from_bounds(left_start, right_end),
        )
    } else if right_then_left.is_proven() {
        (
            ObligationStatus::Proven,
            AbstractByteRange::from_bounds(right_start, left_end),
        )
    } else if left_then_right == ObligationStatus::Refuted
        && right_then_left == ObligationStatus::Refuted
    {
        (ObligationStatus::Refuted, AbstractByteRange::Unknown)
    } else {
        (ObligationStatus::Unknown, AbstractByteRange::Unknown)
    }
}

fn combine_statuses<const N: usize>(statuses: [ObligationStatus; N]) -> ObligationStatus {
    if statuses.contains(&ObligationStatus::Refuted) {
        ObligationStatus::Refuted
    } else if statuses.iter().all(|status| status.is_proven()) {
        ObligationStatus::Proven
    } else {
        ObligationStatus::Unknown
    }
}

fn offset_alignment(base: GuaranteedAlignment, delta: U64Interval) -> GuaranteedAlignment {
    let Some(delta) = delta.exact_value() else {
        return GuaranteedAlignment::one();
    };
    if delta == 0 {
        return base;
    }
    let delta_alignment = 1_u64 << delta.trailing_zeros();
    GuaranteedAlignment::new(delta_alignment)
        .map_or(GuaranteedAlignment::one(), |alignment| base.join(alignment))
}
