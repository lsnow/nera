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
mod loan;
mod object;
mod obligation;
mod permission;
mod pointer;
mod spec;
pub(super) use spec::{
    SpecFootprint, SpecMemoryQuery, query_spec_memory, spec_alive, spec_footprint,
    spec_same_allocation,
};
#[cfg(test)]
mod tests;
mod value;

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
