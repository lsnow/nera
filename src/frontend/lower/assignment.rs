//! Post-CFG initialization planning for assignments and cleanup intents.
//!
//! HIR lowering records one state-neutral assignment operation.  This pass is
//! the only producer that selects VIR initialize/replace modes, after every
//! reachable predecessor and loop back-edge is available. Cleanup is selected
//! from the same canonical type/shape queries and applied in the same traversal;
//! no later pass substitutes a different retirement effect.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::draft::{
    DraftBlock, DraftInstruction, PendingAssignment, PendingAssignmentSource, PendingEffect,
};
use super::invalid_hir;
use crate::ByteSpan;
use crate::frontend::FrontendFailure;
use crate::vir::{
    SpannedVirInstruction, VirBlockId, VirBlockTarget, VirConstant, VirIndexBounds, VirInstruction,
    VirMemoryAccess, VirMemorySchema, VirObjectDestinationMode, VirObjectPathSegment,
    VirObjectSourceMode, VirTerminator, VirType, VirValueId, VirVariantId,
};

const MAX_TRACKED_STORAGE_BYTES: usize = 65_536;
const MAX_ACTIVE_VARIANTS: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum StorageId {
    Parameter(VirValueId),
    Heap(VirValueId),
    Local(VirValueId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ByteState {
    Uninitialized,
    Initialized,
    Unknown,
}

impl ByteState {
    const fn join(self, other: Self) -> Self {
        if matches!(
            (self, other),
            (Self::Initialized, Self::Initialized)
                | (Self::Uninitialized, Self::Uninitialized)
                | (Self::Unknown, Self::Unknown)
        ) {
            self
        } else {
            Self::Unknown
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum VariantState {
    Exact(VirVariantId),
    Alternatives(BTreeSet<VirVariantId>),
    Unknown,
}

impl VariantState {
    fn alternatives(&self) -> Option<BTreeSet<VirVariantId>> {
        match self {
            Self::Exact(variant) => Some(BTreeSet::from([*variant])),
            Self::Alternatives(variants) => Some(variants.clone()),
            Self::Unknown => None,
        }
    }

    fn join(left: Option<&Self>, right: Option<&Self>) -> Option<Self> {
        let (Some(left), Some(right)) = (left, right) else {
            return match (left, right) {
                (None, None) => None,
                _ => Some(Self::Unknown),
            };
        };
        if left == right {
            return Some(left.clone());
        }
        let Some(mut alternatives) = left.alternatives() else {
            return Some(Self::Unknown);
        };
        let Some(right) = right.alternatives() else {
            return Some(Self::Unknown);
        };
        alternatives.extend(right);
        if alternatives.len() > MAX_ACTIVE_VARIANTS {
            Some(Self::Unknown)
        } else if alternatives.len() == 1 {
            alternatives.iter().next().copied().map(Self::Exact)
        } else {
            Some(Self::Alternatives(alternatives))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct StorageState {
    bytes: Vec<ByteState>,
    active_variants: BTreeMap<(u64, VirMemoryAccess), VariantState>,
    resource_values: BTreeMap<(u64, VirMemoryAccess), ValueFact>,
}

impl StorageState {
    fn fresh(size_bytes: u64) -> Option<Self> {
        let size = usize::try_from(size_bytes).ok()?;
        (size <= MAX_TRACKED_STORAGE_BYTES).then(|| Self {
            bytes: vec![ByteState::Uninitialized; size],
            active_variants: BTreeMap::new(),
            resource_values: BTreeMap::new(),
        })
    }

    fn join(&self, other: &Self) -> Option<Self> {
        if self.bytes.len() != other.bytes.len() {
            return None;
        }
        let bytes = self
            .bytes
            .iter()
            .zip(&other.bytes)
            .map(|(left, right)| left.join(*right))
            .collect();
        let keys = self
            .active_variants
            .keys()
            .chain(other.active_variants.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        let active_variants = keys
            .into_iter()
            .filter_map(|key| {
                VariantState::join(
                    self.active_variants.get(&key),
                    other.active_variants.get(&key),
                )
                .map(|state| (key, state))
            })
            .collect();
        let resource_keys = self
            .resource_values
            .keys()
            .chain(other.resource_values.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        let resource_values = resource_keys
            .into_iter()
            .map(|key| {
                let left = self
                    .resource_values
                    .get(&key)
                    .copied()
                    .unwrap_or(ValueFact::Unknown);
                let right = other
                    .resource_values
                    .get(&key)
                    .copied()
                    .unwrap_or(ValueFact::Unknown);
                (key, left.join(right))
            })
            .collect();
        Some(Self {
            bytes,
            active_variants,
            resource_values,
        })
    }

    fn classify(&self, ranges: &[(u64, u64)]) -> ByteState {
        let mut classification = None;
        for (start, end) in ranges {
            let Some(bytes) = self.byte_range(*start, *end) else {
                return ByteState::Unknown;
            };
            for byte in bytes {
                classification = Some(match classification {
                    None => *byte,
                    Some(previous) if previous == *byte => previous,
                    Some(_) => ByteState::Unknown,
                });
                if classification == Some(ByteState::Unknown) {
                    return ByteState::Unknown;
                }
            }
        }
        classification.unwrap_or(ByteState::Uninitialized)
    }

    fn set_ranges(&mut self, ranges: &[(u64, u64)], state: ByteState) -> bool {
        for (start, end) in ranges {
            let Some(bytes) = self.byte_range_mut(*start, *end) else {
                return false;
            };
            bytes.fill(state);
        }
        true
    }

    fn contains_ranges(&self, ranges: &[(u64, u64)]) -> bool {
        ranges
            .iter()
            .all(|(start, end)| self.byte_range(*start, *end).is_some())
    }

    fn byte_range(&self, start: u64, end: u64) -> Option<&[ByteState]> {
        let start = usize::try_from(start).ok()?;
        let end = usize::try_from(end).ok()?;
        self.bytes.get(start..end)
    }

    fn byte_range_mut(&mut self, start: u64, end: u64) -> Option<&mut [ByteState]> {
        let start = usize::try_from(start).ok()?;
        let end = usize::try_from(end).ok()?;
        self.bytes.get_mut(start..end)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PointerFact {
    storage: StorageId,
    offset_bytes: u64,
    access: VirMemoryAccess,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DynamicPointerFact {
    storage: StorageId,
    base_offset_bytes: u64,
    stride_bytes: u64,
    length: u64,
    access: VirMemoryAccess,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PointerLocation {
    Exact(PointerFact),
    Dynamic(DynamicPointerFact),
}

impl PointerLocation {
    const fn storage(self) -> StorageId {
        match self {
            Self::Exact(pointer) => pointer.storage,
            Self::Dynamic(pointer) => pointer.storage,
        }
    }

    const fn access(self) -> VirMemoryAccess {
        match self {
            Self::Exact(pointer) => pointer.access,
            Self::Dynamic(pointer) => pointer.access,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueFact {
    U64(u64),
    Pointer(PointerFact),
    DynamicPointer(DynamicPointerFact),
    Unknown,
}

impl ValueFact {
    fn join(self, other: Self) -> Self {
        if matches!((self, other), (Self::U64(left), Self::U64(right)) if left == right)
            || matches!((self, other), (Self::Pointer(left), Self::Pointer(right)) if left == right)
            || matches!((self, other), (Self::DynamicPointer(left), Self::DynamicPointer(right)) if left == right)
            || matches!((self, other), (Self::Unknown, Self::Unknown))
        {
            self
        } else {
            Self::Unknown
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FlowState {
    values: BTreeMap<VirValueId, ValueFact>,
    storages: BTreeMap<StorageId, StorageState>,
}

impl FlowState {
    fn merge(&self, other: &Self) -> Self {
        let value_keys = self
            .values
            .keys()
            .chain(other.values.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        let values = value_keys
            .into_iter()
            .map(|key| {
                let left = self.values.get(&key).copied().unwrap_or(ValueFact::Unknown);
                let right = other
                    .values
                    .get(&key)
                    .copied()
                    .unwrap_or(ValueFact::Unknown);
                (key, left.join(right))
            })
            .collect();
        let storages = self
            .storages
            .iter()
            .filter_map(|(id, left)| {
                other
                    .storages
                    .get(id)
                    .and_then(|right| left.join(right))
                    .map(|joined| (*id, joined))
            })
            .collect();
        Self { values, storages }
    }
}

#[derive(Clone, Debug)]
struct ObjectMask {
    possible: Vec<(u64, u64)>,
    variants: Vec<(u64, VirMemoryAccess, VariantState)>,
}

pub(super) fn plan_initialization_effects(
    memory: &VirMemorySchema,
    blocks: &mut [DraftBlock],
    source_span: ByteSpan,
    abi: Option<&crate::VirAbiSignature>,
) -> Result<(), FrontendFailure> {
    for block in blocks.iter() {
        if block.terminator.is_none() {
            return Err(invalid_hir(source_span));
        }
    }
    let mut entry = FlowState::default();
    if let Some(abi) = abi {
        for binding in abi
            .parameters()
            .iter()
            .filter(|binding| binding.interface().transfer.is_borrow())
        {
            if let crate::VirAbiValue::Pointer { pointee, .. } = binding.value() {
                let pointer = blocks[0].parameters[binding.parameter_slots()[0] as usize].id;
                let storage = StorageId::Parameter(pointer);
                if let Some(mut bytes) = memory
                    .layout(pointee.layout)
                    .and_then(|layout| StorageState::fresh(layout.size_bytes))
                {
                    bytes.bytes.fill(ByteState::Initialized);
                    entry.storages.insert(storage, bytes);
                    entry.values.insert(
                        pointer,
                        ValueFact::Pointer(PointerFact {
                            storage,
                            offset_bytes: 0,
                            access: *pointee,
                        }),
                    );
                }
            }
        }
    }
    let entries = analyze(memory, blocks, source_span, entry)?;

    for block in blocks {
        let mut state = entries
            .get(block.id.get() as usize)
            .and_then(Clone::clone)
            .unwrap_or_default();
        let reachable = entries
            .get(block.id.get() as usize)
            .is_some_and(Option::is_some);
        let mut instructions = Vec::with_capacity(block.instructions.len());
        for pending in std::mem::take(&mut block.instructions) {
            match pending {
                DraftInstruction::Canonical(instruction) => {
                    apply_ready(memory, &mut state, &instruction.instruction);
                    instructions.push(DraftInstruction::Canonical(instruction));
                }
                DraftInstruction::Pending(PendingEffect::Assignment(assignment)) => {
                    let instruction =
                        refine_assignment(memory, &mut state, &assignment, reachable)?;
                    instructions.push(DraftInstruction::Canonical(Box::new(
                        SpannedVirInstruction {
                            instruction,
                            source_span: assignment.source_span,
                        },
                    )));
                }
                DraftInstruction::Pending(PendingEffect::Cleanup(cleanup)) => {
                    let instruction = super::cleanup::plan_effect(memory, &cleanup)?;
                    apply_ready(memory, &mut state, &instruction.instruction);
                    instructions.push(DraftInstruction::Canonical(Box::new(instruction)));
                }
                DraftInstruction::Pending(effect) => {
                    let instruction = effect
                        .determined_instruction()
                        .ok_or_else(|| invalid_hir(effect.identity().source_span))?;
                    apply_ready(memory, &mut state, &instruction.instruction);
                    instructions.push(DraftInstruction::Pending(effect));
                }
            }
        }
        block.instructions = instructions;
    }
    Ok(())
}

fn analyze(
    memory: &VirMemorySchema,
    blocks: &[DraftBlock],
    source_span: ByteSpan,
    entry: FlowState,
) -> Result<Vec<Option<FlowState>>, FrontendFailure> {
    if blocks.is_empty() || blocks[0].id != VirBlockId::new(0) {
        return Err(invalid_hir(source_span));
    }
    let mut entries = vec![None; blocks.len()];
    entries[0] = Some(entry);
    let mut work = VecDeque::from([VirBlockId::new(0)]);

    while let Some(block_id) = work.pop_front() {
        let block = blocks
            .get(block_id.get() as usize)
            .filter(|block| block.id == block_id)
            .ok_or_else(|| invalid_hir(source_span))?;
        let mut state = entries[block_id.get() as usize]
            .clone()
            .ok_or_else(|| invalid_hir(source_span))?;
        for pending in &block.instructions {
            match pending {
                DraftInstruction::Canonical(instruction) => {
                    apply_ready(memory, &mut state, &instruction.instruction)
                }
                DraftInstruction::Pending(PendingEffect::Assignment(assignment)) => {
                    apply_assignment(memory, &mut state, assignment)
                }
                DraftInstruction::Pending(PendingEffect::Cleanup(cleanup)) => {
                    let instruction = super::cleanup::plan_effect(memory, cleanup)?;
                    apply_ready(memory, &mut state, &instruction.instruction);
                }
                DraftInstruction::Pending(effect) => {
                    let instruction = effect
                        .determined_instruction()
                        .ok_or_else(|| invalid_hir(effect.identity().source_span))?;
                    apply_ready(memory, &mut state, &instruction.instruction);
                }
            }
        }
        let terminator = &block
            .terminator
            .as_ref()
            .ok_or_else(|| invalid_hir(source_span))?
            .terminator;
        for target in successors(terminator) {
            let target_block = blocks
                .get(target.block.get() as usize)
                .filter(|block| block.id == target.block)
                .ok_or_else(|| invalid_hir(source_span))?;
            if target.arguments.len() != target_block.parameters.len() {
                return Err(invalid_hir(source_span));
            }
            let mut edge = FlowState {
                values: BTreeMap::new(),
                storages: state.storages.clone(),
            };
            for (argument, parameter) in target.arguments.iter().zip(&target_block.parameters) {
                if parameter.ty == VirType::Permission {
                    continue;
                }
                edge.values.insert(
                    parameter.id,
                    state
                        .values
                        .get(argument)
                        .copied()
                        .unwrap_or(ValueFact::Unknown),
                );
            }
            let slot = &mut entries[target.block.get() as usize];
            let merged = slot
                .as_ref()
                .map_or_else(|| edge.clone(), |previous| previous.merge(&edge));
            if slot.as_ref() != Some(&merged) {
                *slot = Some(merged);
                if !work.contains(&target.block) {
                    work.push_back(target.block);
                }
            }
        }
    }
    Ok(entries)
}

fn successors(terminator: &VirTerminator) -> Vec<&VirBlockTarget> {
    match terminator {
        VirTerminator::Jump { target } => vec![target],
        VirTerminator::Branch {
            then_target,
            else_target,
            ..
        } => vec![then_target, else_target],
        VirTerminator::Return { .. } => Vec::new(),
    }
}

fn apply_ready(memory: &VirMemorySchema, state: &mut FlowState, instruction: &VirInstruction) {
    match instruction {
        VirInstruction::Constant {
            result,
            value: VirConstant::U64(value),
        } => {
            state.values.insert(result.id, ValueFact::U64(*value));
        }
        VirInstruction::Constant { result, .. }
        | VirInstruction::WordAdd { result, .. }
        | VirInstruction::Compare { result, .. }
        | VirInstruction::PointerCompare { result, .. }
        | VirInstruction::PointerDistance { result, .. }
        | VirInstruction::Load { result, .. }
        | VirInstruction::EnumDiscriminant { result, .. }
        | VirInstruction::PermissionJoin { result, .. }
        | VirInstruction::PermissionMove { result, .. } => {
            state.values.insert(result.id, ValueFact::Unknown);
        }
        VirInstruction::LoanBegin {
            effect,
            reference_result,
            ..
        }
        | VirInstruction::LoanAliasShared {
            effect,
            reference_result,
            ..
        }
        | VirInstruction::LoanReborrow {
            effect,
            reference_result,
            ..
        } => {
            let fact = state
                .values
                .get(&effect.source_pointer)
                .copied()
                .unwrap_or(ValueFact::Unknown);
            state.values.insert(reference_result.id, fact);
        }
        VirInstruction::LoanAliasAuthority {
            effect,
            reference_result,
            ..
        }
        | VirInstruction::LoanReborrowAuthority {
            effect,
            reference_result,
            ..
        } => {
            let fact = state
                .values
                .get(&effect.source_pointer)
                .copied()
                .unwrap_or(ValueFact::Unknown);
            state.values.insert(reference_result.id, fact);
        }
        VirInstruction::ResourceTake {
            pointer_result,
            source,
            access,
            ..
        } => {
            let value = pointer_fact(state, *source)
                .and_then(|pointer| {
                    state
                        .storages
                        .get_mut(&pointer.storage)?
                        .resource_values
                        .remove(&(pointer.offset_bytes, *access))
                })
                .unwrap_or(ValueFact::Unknown);
            state.values.insert(pointer_result.id, value);
            set_scalar(memory, state, *source, *access, ByteState::Uninitialized);
        }
        VirInstruction::LocalStorage {
            pointer_result,
            access,
            ..
        } => {
            if let Ok(shape) = memory.object_shape(*access)
                && let Some(storage) = StorageState::fresh(shape.size_bytes())
            {
                let id = StorageId::Local(pointer_result.id);
                state.storages.insert(id, storage);
                state.values.insert(
                    pointer_result.id,
                    ValueFact::Pointer(PointerFact {
                        storage: id,
                        offset_bytes: 0,
                        access: *access,
                    }),
                );
            }
        }
        VirInstruction::Allocate {
            pointer_result,
            size_bytes,
            element,
            ..
        } => {
            let size = state.values.get(size_bytes).and_then(|fact| match fact {
                ValueFact::U64(value) => Some(*value),
                ValueFact::Pointer(_) | ValueFact::DynamicPointer(_) | ValueFact::Unknown => None,
            });
            if let Some(storage) = size.and_then(StorageState::fresh) {
                let id = StorageId::Heap(pointer_result.id);
                state.storages.insert(id, storage);
                state.values.insert(
                    pointer_result.id,
                    ValueFact::Pointer(PointerFact {
                        storage: id,
                        offset_bytes: 0,
                        access: *element,
                    }),
                );
            }
        }
        VirInstruction::FieldAddress {
            result,
            base,
            field_access,
            offset_bytes,
            ..
        } => derive_pointer(state, result.id, *base, *field_access, *offset_bytes),
        VirInstruction::TupleElementAddress {
            result,
            base,
            element_access,
            offset_bytes,
            ..
        } => derive_pointer(state, result.id, *base, *element_access, *offset_bytes),
        VirInstruction::ObjectLeafAddress {
            result,
            base,
            leaf,
            offset_bytes,
            ..
        } => derive_pointer(state, result.id, *base, *leaf, *offset_bytes),
        VirInstruction::IndexAddress {
            result,
            base,
            index,
            element,
            stride_bytes,
            bounds: VirIndexBounds::Array { length },
            ..
        } => {
            let offset = state.values.get(index).and_then(|fact| match fact {
                ValueFact::U64(index) if index < length => index.checked_mul(*stride_bytes),
                ValueFact::U64(_)
                | ValueFact::Pointer(_)
                | ValueFact::DynamicPointer(_)
                | ValueFact::Unknown => None,
            });
            if let Some(offset) = offset {
                derive_pointer(state, result.id, *base, *element, offset);
            } else {
                let dynamic = state.values.get(base).and_then(|fact| match fact {
                    ValueFact::Pointer(pointer) => Some(DynamicPointerFact {
                        storage: pointer.storage,
                        base_offset_bytes: pointer.offset_bytes,
                        stride_bytes: *stride_bytes,
                        length: *length,
                        access: *element,
                    }),
                    ValueFact::U64(_) | ValueFact::DynamicPointer(_) | ValueFact::Unknown => None,
                });
                state.values.insert(
                    result.id,
                    dynamic.map_or(ValueFact::Unknown, ValueFact::DynamicPointer),
                );
            }
        }
        VirInstruction::IndexAddress {
            result,
            base,
            index,
            element,
            stride_bytes,
            bounds: VirIndexBounds::Slice { length },
            ..
        } => {
            let index = state.values.get(index).and_then(exact_word_fact);
            let length = state.values.get(length).and_then(exact_word_fact);
            if let (Some(index), Some(length)) = (index, length)
                && index < length
                && let Some(offset) = index.checked_mul(*stride_bytes)
            {
                derive_pointer(state, result.id, *base, *element, offset);
            } else {
                state.values.insert(result.id, ValueFact::Unknown);
            }
        }
        VirInstruction::SliceRange {
            pointer_result,
            length_result,
            base,
            start,
            end,
            element,
            stride_bytes,
            bounds,
            ..
        }
        | VirInstruction::SliceAddress {
            pointer_result,
            length_result,
            base,
            start,
            end,
            element,
            stride_bytes,
            bounds,
            ..
        } => {
            let start = state.values.get(start).and_then(exact_word_fact);
            let end = state.values.get(end).and_then(exact_word_fact);
            let bound = match bounds {
                VirIndexBounds::Array { length } => Some(*length),
                VirIndexBounds::Slice { length } => {
                    state.values.get(length).and_then(exact_word_fact)
                }
            };
            if let (Some(start), Some(end), Some(bound)) = (start, end, bound)
                && start <= end
                && end <= bound
                && let Some(offset) = start.checked_mul(*stride_bytes)
            {
                derive_pointer(state, pointer_result.id, *base, *element, offset);
                state
                    .values
                    .insert(length_result.id, ValueFact::U64(end - start));
            } else {
                state.values.insert(pointer_result.id, ValueFact::Unknown);
                state.values.insert(length_result.id, ValueFact::Unknown);
            }
        }
        VirInstruction::RawAddress { result, base, .. } => {
            let fact = state
                .values
                .get(base)
                .copied()
                .unwrap_or(ValueFact::Unknown);
            state.values.insert(result.id, fact);
        }
        VirInstruction::PointerOffset {
            result,
            base,
            delta_bytes,
        } => {
            let offset = state.values.get(delta_bytes).and_then(|fact| match fact {
                ValueFact::U64(offset) => Some(*offset),
                ValueFact::Pointer(_) | ValueFact::DynamicPointer(_) | ValueFact::Unknown => None,
            });
            let access = state.values.get(base).and_then(|fact| match fact {
                ValueFact::Pointer(pointer) => Some(pointer.access),
                ValueFact::DynamicPointer(pointer) => Some(pointer.access),
                ValueFact::U64(_) | ValueFact::Unknown => None,
            });
            if let (Some(offset), Some(access)) = (offset, access) {
                derive_pointer(state, result.id, *base, access, offset);
            } else {
                state.values.insert(result.id, ValueFact::Unknown);
            }
        }
        VirInstruction::Initialize {
            pointer, access, ..
        }
        | VirInstruction::Write {
            pointer, access, ..
        }
        | VirInstruction::Store {
            pointer, access, ..
        } => set_scalar(memory, state, *pointer, *access, ByteState::Initialized),
        VirInstruction::ResourceInitialize {
            destination,
            value,
            access,
            ..
        } => {
            let payload = state
                .values
                .get(value)
                .copied()
                .unwrap_or(ValueFact::Unknown);
            if let Some(pointer) = pointer_fact(state, *destination)
                && let Some(storage) = state.storages.get_mut(&pointer.storage)
            {
                storage
                    .resource_values
                    .insert((pointer.offset_bytes, *access), payload);
            }
            set_scalar(memory, state, *destination, *access, ByteState::Initialized);
        }
        VirInstruction::ObjectTransfer {
            destination,
            source,
            access,
            source_mode,
            ..
        } => apply_object_transfer(memory, state, *destination, *source, *access, *source_mode),
        VirInstruction::ObjectDeinitialize {
            pointer, access, ..
        }
        | VirInstruction::StorageReset {
            pointer, access, ..
        }
        | VirInstruction::ResourceStorageReset {
            pointer, access, ..
        }
        | VirInstruction::ObjectDrop {
            pointer, access, ..
        } => {
            if let Some((fact, mask)) = object_mask(memory, state, *pointer, *access) {
                if let Some(storage) = state.storages.get_mut(&fact.storage) {
                    let ranges = absolute_ranges(fact.offset_bytes, &mask.possible);
                    storage.set_ranges(&ranges, ByteState::Uninitialized);
                    forget_variants(storage, fact.offset_bytes, *access, memory);
                    forget_resource_values(storage, fact.offset_bytes, *access, memory);
                }
            }
        }
        VirInstruction::EnumSetDiscriminant {
            pointer,
            access,
            variant,
            ..
        } => apply_discriminant(memory, state, *pointer, *access, *variant),
        VirInstruction::Call {
            target,
            arguments,
            results,
        } => {
            if let Some(abi) = &target.abi {
                if let Some(index) = abi.borrow_result_parameter() {
                    let relation = abi.borrow_result().expect("borrow result parameter exists");
                    let source = &abi.parameters()[index];
                    let result = &abi.results()[relation.result as usize];
                    match relation.projection {
                        crate::BorrowProjection::Whole => {
                            for (slot, input_slot) in
                                result.result_slots().iter().zip(source.parameter_slots())
                            {
                                let fact = state
                                    .values
                                    .get(&arguments[*input_slot as usize])
                                    .copied()
                                    .unwrap_or(ValueFact::Unknown);
                                state.values.insert(results[*slot as usize].id, fact);
                            }
                        }
                        crate::BorrowProjection::Fixed { offset_bytes, .. } => {
                            if let (
                                Some(source_slot),
                                Some(result_slot),
                                crate::VirAbiValue::Pointer { pointee, .. },
                            ) = (
                                source.parameter_slots().first(),
                                result.result_slots().first(),
                                result.value(),
                            ) {
                                derive_pointer(
                                    state,
                                    results[*result_slot as usize].id,
                                    arguments[*source_slot as usize],
                                    *pointee,
                                    offset_bytes,
                                );
                            }
                        }
                        crate::BorrowProjection::Slice {
                            start,
                            end,
                            stride_bytes,
                            ..
                        } => {
                            let bound = |bound: crate::BorrowSliceBound,
                                         state: &FlowState|
                             -> Option<u64> {
                                match bound {
                                    crate::BorrowSliceBound::Constant(value) => Some(value),
                                    crate::BorrowSliceBound::Parameter(parameter) => {
                                        let binding = abi.parameters().get(parameter as usize)?;
                                        state
                                            .values
                                            .get(
                                                &arguments
                                                    [*binding.parameter_slots().first()? as usize],
                                            )
                                            .and_then(exact_word_fact)
                                    }
                                    crate::BorrowSliceBound::SourceLength => state
                                        .values
                                        .get(&arguments[*source.parameter_slots().get(1)? as usize])
                                        .and_then(exact_word_fact),
                                }
                            };
                            let projected = bound(start, state).zip(bound(end, state));
                            let slots = result.result_slots();
                            let element = match result.value() {
                                crate::VirAbiValue::Slice { element, .. } => Some(*element),
                                _ => None,
                            };
                            if let (Some((start, end)), Some(element), Some(pointer), Some(length)) =
                                (projected, element, slots.first(), slots.get(1))
                                && start <= end
                                && let Some(offset) = start.checked_mul(stride_bytes)
                            {
                                derive_pointer(
                                    state,
                                    results[*pointer as usize].id,
                                    arguments[source.parameter_slots()[0] as usize],
                                    element,
                                    offset,
                                );
                                state.values.insert(
                                    results[*length as usize].id,
                                    ValueFact::U64(end - start),
                                );
                            } else {
                                for slot in slots.iter().take(2) {
                                    state
                                        .values
                                        .insert(results[*slot as usize].id, ValueFact::Unknown);
                                }
                            }
                        }
                    }
                }
                for binding in abi.results() {
                    if let crate::VirAbiValue::IndirectAggregate { access } = binding.value()
                        && let [pointer_slot, _permission_slot] = binding.parameter_slots()
                        && let Some(pointer) = arguments.get(*pointer_slot as usize)
                    {
                        set_object_initialization(
                            memory,
                            state,
                            *pointer,
                            *access,
                            ByteState::Initialized,
                        );
                    }
                }
            }
        }
        VirInstruction::PermissionSplit { .. }
        | VirInstruction::LoanEnd { .. }
        | VirInstruction::LoanEndAuthority { .. }
        | VirInstruction::DropOwn { .. }
        | VirInstruction::Free { .. }
        | VirInstruction::Check { .. } => {}
    }
}

fn exact_word_fact(fact: &ValueFact) -> Option<u64> {
    match fact {
        ValueFact::U64(value) => Some(*value),
        ValueFact::Pointer(_) | ValueFact::DynamicPointer(_) | ValueFact::Unknown => None,
    }
}

fn derive_pointer(
    state: &mut FlowState,
    result: VirValueId,
    base: VirValueId,
    access: VirMemoryAccess,
    offset_bytes: u64,
) {
    let derived = state.values.get(&base).and_then(|fact| match fact {
        ValueFact::Pointer(pointer) => {
            pointer
                .offset_bytes
                .checked_add(offset_bytes)
                .map(|offset_bytes| PointerFact {
                    storage: pointer.storage,
                    offset_bytes,
                    access,
                })
        }
        ValueFact::U64(_) | ValueFact::DynamicPointer(_) | ValueFact::Unknown => None,
    });
    if let Some(pointer) = derived {
        state.values.insert(result, ValueFact::Pointer(pointer));
        return;
    }
    let dynamic = state.values.get(&base).and_then(|fact| match fact {
        ValueFact::DynamicPointer(pointer) => pointer
            .base_offset_bytes
            .checked_add(offset_bytes)
            .map(|base_offset_bytes| DynamicPointerFact {
                storage: pointer.storage,
                base_offset_bytes,
                stride_bytes: pointer.stride_bytes,
                length: pointer.length,
                access,
            }),
        ValueFact::U64(_) | ValueFact::Pointer(_) | ValueFact::Unknown => None,
    });
    state.values.insert(
        result,
        dynamic.map_or(ValueFact::Unknown, ValueFact::DynamicPointer),
    );
}

fn apply_assignment(
    memory: &VirMemorySchema,
    state: &mut FlowState,
    assignment: &PendingAssignment,
) {
    match assignment.source {
        PendingAssignmentSource::Scalar { .. } => set_scalar(
            memory,
            state,
            assignment.destination,
            assignment.access,
            ByteState::Initialized,
        ),
        PendingAssignmentSource::Object { pointer, mode, .. } => apply_object_transfer(
            memory,
            state,
            assignment.destination,
            pointer,
            assignment.access,
            mode,
        ),
    }
}

fn refine_assignment(
    memory: &VirMemorySchema,
    state: &mut FlowState,
    assignment: &PendingAssignment,
    reachable: bool,
) -> Result<VirInstruction, FrontendFailure> {
    let mode = if reachable {
        classify_destination(memory, state, assignment)?
    } else {
        Some(VirObjectDestinationMode::Initialize)
    };
    let instruction = match assignment.source {
        PendingAssignmentSource::Scalar { value } => match mode {
            Some(VirObjectDestinationMode::Initialize) => VirInstruction::Initialize {
                pointer: assignment.destination,
                value,
                permission: assignment.destination_permission,
                access: assignment.access,
            },
            Some(VirObjectDestinationMode::Replace) => VirInstruction::Store {
                pointer: assignment.destination,
                value,
                permission: assignment.destination_permission,
                access: assignment.access,
            },
            None => VirInstruction::Write {
                pointer: assignment.destination,
                value,
                permission: assignment.destination_permission,
                access: assignment.access,
            },
        },
        PendingAssignmentSource::Object {
            pointer,
            permission,
            mode: source_mode,
        } => VirInstruction::ObjectTransfer {
            destination: assignment.destination,
            destination_permission: assignment.destination_permission,
            source: pointer,
            source_permission: permission,
            access: assignment.access,
            destination_mode: mode.ok_or_else(|| initialization_unknown(assignment.source_span))?,
            source_mode,
        },
    };
    apply_assignment(memory, state, assignment);
    Ok(instruction)
}

fn classify_destination(
    memory: &VirMemorySchema,
    state: &FlowState,
    assignment: &PendingAssignment,
) -> Result<Option<VirObjectDestinationMode>, FrontendFailure> {
    let Some(pointer) = pointer_location(state, assignment.destination) else {
        return Ok(None);
    };
    if pointer.access() != assignment.access {
        return Err(invalid_hir(assignment.source_span));
    }
    let Some(storage) = state.storages.get(&pointer.storage()) else {
        return Ok(None);
    };
    let relative = match assignment.source {
        PendingAssignmentSource::Scalar { .. } => {
            let layout = memory
                .layout(assignment.access.layout)
                .filter(|layout| layout.ty == assignment.access.ty)
                .ok_or_else(|| invalid_hir(assignment.source_span))?;
            vec![(0, layout.size_bytes)]
        }
        PendingAssignmentSource::Object {
            pointer: source, ..
        } => match object_mask_any(memory, state, source, assignment.access)
            .map(|(_source_pointer, source_mask)| source_mask.possible)
            .or_else(|| static_variant_free_object_ranges(memory, assignment.access))
        {
            Some(ranges) => ranges,
            None => return Ok(None),
        },
    };
    let Some(initialize_ranges) = location_ranges(pointer, &relative) else {
        return match pointer {
            PointerLocation::Exact(_) => Ok(Some(VirObjectDestinationMode::Initialize)),
            PointerLocation::Dynamic(_) => Ok(None),
        };
    };
    // Initialization refinement does not prove address bounds. Preserve an
    // explicit first-write intent for an exact but invalid address so the VIR
    // verifier/interpreter can report the independent bounds fault. Unknown
    // initialization inside a valid extent is left unclassified; only a
    // state-independent trivial Write may use that result without refinement.
    if !storage.contains_ranges(&initialize_ranges) {
        return Ok(Some(VirObjectDestinationMode::Initialize));
    }
    if storage.classify(&initialize_ranges) == ByteState::Uninitialized {
        return Ok(Some(VirObjectDestinationMode::Initialize));
    }
    let replace_relative = match assignment.source {
        PendingAssignmentSource::Scalar { .. } => relative,
        PendingAssignmentSource::Object { .. } => {
            let Some((_, mask)) =
                object_mask_any(memory, state, assignment.destination, assignment.access)
            else {
                return Ok(None);
            };
            mask.possible
        }
    };
    let Some(replace_ranges) = location_ranges(pointer, &replace_relative) else {
        return Ok(None);
    };
    if storage.classify(&replace_ranges) == ByteState::Initialized {
        Ok(Some(VirObjectDestinationMode::Replace))
    } else {
        Ok(None)
    }
}

fn initialization_unknown(span: ByteSpan) -> FrontendFailure {
    FrontendFailure::unsupported(
        span,
        "post-CFG initialization planning lacks definite destination state or exceeds its analysis budget",
    )
}

fn static_variant_free_object_ranges(
    memory: &VirMemorySchema,
    access: VirMemoryAccess,
) -> Option<Vec<(u64, u64)>> {
    let shape = memory.object_shape(access).ok()?;
    if !shape.variants().is_empty() {
        return None;
    }
    let mut ranges = shape
        .leaves()
        .iter()
        .map(|leaf| (leaf.bytes().start_bytes(), leaf.bytes().end_bytes()))
        .collect::<Vec<_>>();
    canonicalize_ranges(&mut ranges);
    Some(ranges)
}

fn set_scalar(
    memory: &VirMemorySchema,
    state: &mut FlowState,
    pointer: VirValueId,
    access: VirMemoryAccess,
    byte_state: ByteState,
) {
    if let Some(pointer) = dynamic_pointer_fact(state, pointer) {
        let Some(layout) = memory
            .layout(access.layout)
            .filter(|layout| layout.ty == access.ty && pointer.access == access)
        else {
            return;
        };
        let Some(ranges) = dynamic_ranges(pointer, &[(0, layout.size_bytes)]) else {
            return;
        };
        if let Some(storage) = state.storages.get_mut(&pointer.storage) {
            for (start, end) in ranges {
                let Some(bytes) = storage.byte_range_mut(start, end) else {
                    return;
                };
                for byte in bytes {
                    *byte = byte.join(byte_state);
                }
            }
        }
        return;
    }
    let Some(pointer) = pointer_fact(state, pointer) else {
        return;
    };
    let Some(layout) = memory
        .layout(access.layout)
        .filter(|layout| layout.ty == access.ty)
    else {
        return;
    };
    let Some(end) = pointer.offset_bytes.checked_add(layout.size_bytes) else {
        return;
    };
    if let Some(storage) = state.storages.get_mut(&pointer.storage) {
        storage.set_ranges(&[(pointer.offset_bytes, end)], byte_state);
    }
}

fn dynamic_ranges(pointer: DynamicPointerFact, relative: &[(u64, u64)]) -> Option<Vec<(u64, u64)>> {
    let capacity = usize::try_from(pointer.length)
        .ok()?
        .checked_mul(relative.len())?;
    if capacity > MAX_TRACKED_STORAGE_BYTES {
        return None;
    }
    let mut ranges = Vec::with_capacity(capacity);
    for index in 0..pointer.length {
        let element_offset = index.checked_mul(pointer.stride_bytes)?;
        let base = pointer.base_offset_bytes.checked_add(element_offset)?;
        for (start, end) in relative {
            ranges.push((base.checked_add(*start)?, base.checked_add(*end)?));
        }
    }
    Some(ranges)
}

fn apply_object_transfer(
    memory: &VirMemorySchema,
    state: &mut FlowState,
    destination: VirValueId,
    source: VirValueId,
    access: VirMemoryAccess,
    source_mode: VirObjectSourceMode,
) {
    let Some(destination_pointer) = pointer_location(state, destination) else {
        return;
    };
    let Some((source_pointer, source_mask)) = object_mask_any(memory, state, source, access) else {
        return;
    };
    let source_initialized = state
        .storages
        .get(&source_pointer.storage())
        .is_some_and(|storage| {
            location_ranges(source_pointer, &source_mask.possible)
                .is_some_and(|ranges| storage.classify(&ranges) == ByteState::Initialized)
        });
    let Some(destination_ranges) = location_ranges(destination_pointer, &source_mask.possible)
    else {
        return;
    };
    let new_state = if source_initialized {
        ByteState::Initialized
    } else {
        ByteState::Unknown
    };
    let resource_values = match (source_pointer, destination_pointer) {
        (PointerLocation::Exact(source), PointerLocation::Exact(destination)) => memory
            .object_shape(access)
            .ok()
            .map(|shape| {
                shape
                    .resource_leaves()
                    .iter()
                    .filter(|leaf| {
                        source_mask.possible.iter().any(|(start, end)| {
                            *start <= leaf.bytes().start_bytes() && leaf.bytes().end_bytes() <= *end
                        })
                    })
                    .filter_map(|leaf| {
                        let source_offset = source
                            .offset_bytes
                            .checked_add(leaf.bytes().start_bytes())?;
                        let destination_offset = destination
                            .offset_bytes
                            .checked_add(leaf.bytes().start_bytes())?;
                        let value = state
                            .storages
                            .get(&source.storage)?
                            .resource_values
                            .get(&(source_offset, leaf.access()))
                            .copied()?;
                        Some((
                            source.storage,
                            (source_offset, leaf.access()),
                            destination.storage,
                            (destination_offset, leaf.access()),
                            value,
                        ))
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default(),
        _ => Vec::new(),
    };
    if let Some(storage) = state.storages.get_mut(&destination_pointer.storage()) {
        match destination_pointer {
            PointerLocation::Exact(pointer) => {
                storage.set_ranges(&destination_ranges, new_state);
                forget_variants(storage, pointer.offset_bytes, access, memory);
                forget_resource_values(storage, pointer.offset_bytes, access, memory);
                for (relative, enum_access, variant) in source_mask.variants {
                    if let Some(offset) = pointer.offset_bytes.checked_add(relative) {
                        storage
                            .active_variants
                            .insert((offset, enum_access), variant);
                    }
                }
            }
            PointerLocation::Dynamic(_) => {
                for (start, end) in destination_ranges {
                    let Some(bytes) = storage.byte_range_mut(start, end) else {
                        return;
                    };
                    for byte in bytes {
                        *byte = byte.join(new_state);
                    }
                }
            }
        }
    }
    for (_, _, destination_storage, destination_key, value) in &resource_values {
        if let Some(storage) = state.storages.get_mut(destination_storage) {
            storage.resource_values.insert(*destination_key, *value);
        }
    }
    if source_mode == VirObjectSourceMode::Move
        && let Some(source_ranges) = location_ranges(source_pointer, &source_mask.possible)
        && let Some(storage) = state.storages.get_mut(&source_pointer.storage())
    {
        storage.set_ranges(&source_ranges, ByteState::Uninitialized);
        if let PointerLocation::Exact(pointer) = source_pointer {
            forget_variants(storage, pointer.offset_bytes, access, memory);
        }
    }
    if source_mode == VirObjectSourceMode::Move {
        for (source_storage, source_key, _, _, _) in resource_values {
            if let Some(storage) = state.storages.get_mut(&source_storage) {
                storage.resource_values.remove(&source_key);
            }
        }
    }
}

fn set_object_initialization(
    memory: &VirMemorySchema,
    state: &mut FlowState,
    pointer: VirValueId,
    access: VirMemoryAccess,
    initialization: ByteState,
) {
    let Some((fact, mask)) = object_mask(memory, state, pointer, access) else {
        return;
    };
    let ranges = absolute_ranges(fact.offset_bytes, &mask.possible);
    if let Some(storage) = state.storages.get_mut(&fact.storage) {
        storage.set_ranges(&ranges, initialization);
        forget_variants(storage, fact.offset_bytes, access, memory);
    }
}

fn apply_discriminant(
    memory: &VirMemorySchema,
    state: &mut FlowState,
    pointer: VirValueId,
    access: VirMemoryAccess,
    variant: VirVariantId,
) {
    let Some(pointer) = pointer_fact(state, pointer) else {
        return;
    };
    let Ok(shape) = memory.object_shape(access) else {
        return;
    };
    let Some(case) = shape
        .variants()
        .iter()
        .find(|case| case.path().segments().is_empty() && case.variant() == variant)
    else {
        return;
    };
    let possible = shape
        .value_bytes()
        .iter()
        .map(|range| (range.start_bytes(), range.end_bytes()))
        .collect::<Vec<_>>();
    let payload = absolute_ranges(pointer.offset_bytes, &possible);
    let Some(tag_start) = pointer.offset_bytes.checked_add(case.tag().start_bytes()) else {
        return;
    };
    let Some(tag_end) = pointer.offset_bytes.checked_add(case.tag().end_bytes()) else {
        return;
    };
    if let Some(storage) = state.storages.get_mut(&pointer.storage) {
        storage.set_ranges(&payload, ByteState::Uninitialized);
        storage.set_ranges(&[(tag_start, tag_end)], ByteState::Initialized);
        forget_variants(storage, pointer.offset_bytes, access, memory);
        forget_resource_values(storage, pointer.offset_bytes, access, memory);
        storage
            .active_variants
            .insert((tag_start, access), VariantState::Exact(variant));
    }
}

fn object_mask(
    memory: &VirMemorySchema,
    state: &FlowState,
    pointer: VirValueId,
    access: VirMemoryAccess,
) -> Option<(PointerFact, ObjectMask)> {
    let pointer = pointer_fact(state, pointer)?;
    if pointer.access != access {
        return None;
    }
    let storage = state.storages.get(&pointer.storage)?;
    let shape = memory.object_shape(access).ok()?;
    let mut grouped =
        BTreeMap::<(Vec<VirObjectPathSegment>, VirMemoryAccess, u64), BTreeSet<VirVariantId>>::new(
        );
    for variant in shape.variants() {
        grouped
            .entry((
                variant.path().segments().to_vec(),
                variant.enum_access(),
                variant.tag().start_bytes(),
            ))
            .or_default()
            .insert(variant.variant());
    }
    let mut sites = grouped.into_iter().collect::<Vec<_>>();
    sites.sort_by(|left, right| {
        left.0
            .0
            .len()
            .cmp(&right.0.0.len())
            .then_with(|| left.0.cmp(&right.0))
    });
    let mut choices = BTreeMap::new();
    let mut variants = Vec::new();
    for ((path, enum_access, relative), declared) in sites {
        if !path_possible(&path, &choices) {
            continue;
        }
        let absolute = pointer.offset_bytes.checked_add(relative)?;
        let variant = storage
            .active_variants
            .get(&(absolute, enum_access))
            .cloned()
            .unwrap_or(VariantState::Unknown);
        let active = variant.alternatives()?;
        if active.is_empty() || !active.is_subset(&declared) {
            return None;
        }
        choices.insert(path, variant.clone());
        variants.push((relative, enum_access, variant));
    }
    let mut possible = Vec::new();
    for leaf in shape.leaves() {
        if path_possible(leaf.path().segments(), &choices) {
            possible.push((leaf.bytes().start_bytes(), leaf.bytes().end_bytes()));
        }
    }
    for variant in shape.variants() {
        if path_possible(variant.path().segments(), &choices) {
            possible.push((variant.tag().start_bytes(), variant.tag().end_bytes()));
        }
    }
    canonicalize_ranges(&mut possible);
    Some((pointer, ObjectMask { possible, variants }))
}

fn object_mask_any(
    memory: &VirMemorySchema,
    state: &FlowState,
    pointer: VirValueId,
    access: VirMemoryAccess,
) -> Option<(PointerLocation, ObjectMask)> {
    if let Some((pointer, mask)) = object_mask(memory, state, pointer, access) {
        return Some((PointerLocation::Exact(pointer), mask));
    }
    let pointer = dynamic_pointer_fact(state, pointer)?;
    if pointer.access != access {
        return None;
    }
    let shape = memory.object_shape(access).ok()?;
    if !shape.variants().is_empty() {
        return None;
    }
    let mut possible = shape
        .leaves()
        .iter()
        .map(|leaf| (leaf.bytes().start_bytes(), leaf.bytes().end_bytes()))
        .collect::<Vec<_>>();
    canonicalize_ranges(&mut possible);
    Some((
        PointerLocation::Dynamic(pointer),
        ObjectMask {
            possible,
            variants: Vec::new(),
        },
    ))
}

fn path_possible(
    path: &[VirObjectPathSegment],
    choices: &BTreeMap<Vec<VirObjectPathSegment>, VariantState>,
) -> bool {
    let mut prefix = Vec::new();
    for segment in path {
        if let VirObjectPathSegment::Variant(variant) = segment {
            match choices.get(&prefix) {
                Some(VariantState::Exact(active)) if active != variant => return false,
                Some(VariantState::Alternatives(active)) if !active.contains(variant) => {
                    return false;
                }
                Some(VariantState::Exact(_) | VariantState::Alternatives(_))
                | Some(VariantState::Unknown)
                | None => {}
            }
        }
        prefix.push(*segment);
    }
    true
}

fn pointer_fact(state: &FlowState, value: VirValueId) -> Option<PointerFact> {
    match state.values.get(&value) {
        Some(ValueFact::Pointer(pointer)) => Some(*pointer),
        Some(ValueFact::U64(_) | ValueFact::DynamicPointer(_) | ValueFact::Unknown) | None => None,
    }
}

fn pointer_location(state: &FlowState, value: VirValueId) -> Option<PointerLocation> {
    pointer_fact(state, value)
        .map(PointerLocation::Exact)
        .or_else(|| dynamic_pointer_fact(state, value).map(PointerLocation::Dynamic))
}

fn dynamic_pointer_fact(state: &FlowState, value: VirValueId) -> Option<DynamicPointerFact> {
    match state.values.get(&value) {
        Some(ValueFact::DynamicPointer(pointer)) => Some(*pointer),
        Some(ValueFact::U64(_) | ValueFact::Pointer(_) | ValueFact::Unknown) | None => None,
    }
}

fn absolute_ranges(base: u64, relative: &[(u64, u64)]) -> Vec<(u64, u64)> {
    relative
        .iter()
        .filter_map(|(start, end)| Some((base.checked_add(*start)?, base.checked_add(*end)?)))
        .collect()
}

fn location_ranges(pointer: PointerLocation, relative: &[(u64, u64)]) -> Option<Vec<(u64, u64)>> {
    match pointer {
        PointerLocation::Exact(pointer) => relative
            .iter()
            .map(|(start, end)| {
                Some((
                    pointer.offset_bytes.checked_add(*start)?,
                    pointer.offset_bytes.checked_add(*end)?,
                ))
            })
            .collect(),
        PointerLocation::Dynamic(pointer) => dynamic_ranges(pointer, relative),
    }
}

fn forget_variants(
    storage: &mut StorageState,
    base: u64,
    access: VirMemoryAccess,
    memory: &VirMemorySchema,
) {
    let Some(size) = memory.layout(access.layout).map(|layout| layout.size_bytes) else {
        return;
    };
    let Some(end) = base.checked_add(size) else {
        return;
    };
    storage
        .active_variants
        .retain(|(offset, _), _| *offset < base || *offset >= end);
}

fn forget_resource_values(
    storage: &mut StorageState,
    base: u64,
    access: VirMemoryAccess,
    memory: &VirMemorySchema,
) {
    let Some(size) = memory.layout(access.layout).map(|layout| layout.size_bytes) else {
        return;
    };
    let Some(end) = base.checked_add(size) else {
        return;
    };
    storage
        .resource_values
        .retain(|(offset, _), _| *offset < base || *offset >= end);
}

fn canonicalize_ranges(ranges: &mut Vec<(u64, u64)>) {
    ranges.sort_unstable();
    let mut output: Vec<(u64, u64)> = Vec::with_capacity(ranges.len());
    for (start, end) in ranges.drain(..) {
        if start == end {
            continue;
        }
        if let Some(last) = output.last_mut()
            && start <= last.1
        {
            last.1 = last.1.max(end);
        } else {
            output.push((start, end));
        }
    }
    *ranges = output;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::hir::HirNodeId;
    use crate::frontend::lower::draft::{
        DraftEffectIdentity, DraftObjectIdentity, DraftSourceIdentity, PendingCleanup,
        PendingCleanupKind,
    };

    fn fixture() -> (FlowState, PendingAssignment) {
        let access = VirMemoryAccess::core_u64();
        let pointer = VirValueId::new(0);
        let storage = StorageId::Local(pointer);
        let mut state = FlowState::default();
        state.values.insert(
            pointer,
            ValueFact::Pointer(PointerFact {
                storage,
                offset_bytes: 0,
                access,
            }),
        );
        state
            .storages
            .insert(storage, StorageState::fresh(8).unwrap());
        let source_span = ByteSpan::new(4, 8).unwrap();
        let assignment = PendingAssignment {
            identity: DraftEffectIdentity {
                source: DraftSourceIdentity::HirNode(HirNodeId::new(0)),
                object: DraftObjectIdentity {
                    pointer,
                    permission: VirValueId::new(1),
                    access,
                },
                source_span,
            },
            destination: pointer,
            destination_permission: VirValueId::new(1),
            access,
            source: PendingAssignmentSource::Scalar {
                value: VirValueId::new(2),
            },
            source_span,
        };
        (state, assignment)
    }

    #[test]
    fn initialization_and_cleanup_use_the_same_ordered_flow_state() {
        let memory = VirMemorySchema::core_u64();
        let (mut state, assignment) = fixture();
        assert!(matches!(
            refine_assignment(&memory, &mut state, &assignment, true).unwrap(),
            VirInstruction::Initialize { .. }
        ));
        assert!(matches!(
            refine_assignment(&memory, &mut state, &assignment, true).unwrap(),
            VirInstruction::Store { .. }
        ));
        let cleanup = PendingCleanup {
            identity: assignment.identity,
            kind: PendingCleanupKind::Object { condition: None },
        };
        let effect = super::super::cleanup::plan_effect(&memory, &cleanup).unwrap();
        let conditional = PendingCleanup {
            kind: PendingCleanupKind::Object {
                condition: Some(VirValueId::new(3)),
            },
            ..cleanup.clone()
        };
        assert!(
            super::super::cleanup::plan_effect(&memory, &conditional).is_err(),
            "a cleanup condition must not be silently discarded"
        );
        assert!(matches!(
            effect.instruction,
            VirInstruction::ObjectDeinitialize { .. }
        ));
        apply_ready(&memory, &mut state, &effect.instruction);
        assert!(matches!(
            refine_assignment(&memory, &mut state, &assignment, true).unwrap(),
            VirInstruction::Initialize { .. }
        ));
    }

    #[test]
    fn mixed_branch_scalar_state_uses_state_independent_write() {
        let memory = VirMemorySchema::core_u64();
        let (uninitialized, assignment) = fixture();
        let mut initialized = uninitialized.clone();
        apply_assignment(&memory, &mut initialized, &assignment);
        let joined = uninitialized.merge(&initialized);
        assert_eq!(
            classify_destination(&memory, &joined, &assignment).unwrap(),
            None
        );
        assert!(matches!(
            refine_assignment(&memory, &mut joined.clone(), &assignment, true).unwrap(),
            VirInstruction::Write { .. }
        ));
        assert_eq!(joined, initialized.merge(&uninitialized));
    }
}
