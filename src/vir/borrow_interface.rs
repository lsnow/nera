//! Independent SSA validation of returned borrowed views.
//!
//! Permission conservation is verified by resource transfer. This pass checks
//! pointer roots plus bounded offset/length equations without trusting the HIR
//! inference that produced the ABI relation.

use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
struct Linear {
    terms: BTreeMap<VirValueId, i128>,
    constant: i128,
}

impl Linear {
    fn input(value: VirValueId) -> Self {
        Self {
            terms: BTreeMap::from([(value, 1)]),
            constant: 0,
        }
    }
    fn constant(value: u64) -> Self {
        Self {
            terms: BTreeMap::new(),
            constant: i128::from(value),
        }
    }
    fn add(&self, other: &Self) -> Option<Self> {
        self.combine(other, 1)
    }
    fn sub(&self, other: &Self) -> Option<Self> {
        self.combine(other, -1)
    }
    fn scale(&self, scale: u64) -> Option<Self> {
        let scale = i128::from(scale);
        Some(Self {
            terms: self
                .terms
                .iter()
                .map(|(value, coefficient)| Some((*value, coefficient.checked_mul(scale)?)))
                .collect::<Option<_>>()?,
            constant: self.constant.checked_mul(scale)?,
        })
    }
    fn combine(&self, other: &Self, sign: i128) -> Option<Self> {
        let mut result = self.clone();
        result.constant = result
            .constant
            .checked_add(other.constant.checked_mul(sign)?)?;
        for (value, coefficient) in &other.terms {
            let coefficient = coefficient.checked_mul(sign)?;
            let total = result.terms.entry(*value).or_default();
            *total = total.checked_add(coefficient)?;
            if *total == 0 {
                result.terms.remove(value);
            }
        }
        Some(result)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct PointerView {
    root: VirValueId,
    /// A typed reference leaf loaded from this input storage root. This is
    /// source evidence only; CFG transfer independently checks the actual loan.
    field: Option<(u64, VirMemoryAccess)>,
    offset: Linear,
    /// Length paired with this pointer by a slice constructor or checked call.
    slice_length: Option<Linear>,
}

type Cell = (VirValueId, u64, VirMemoryAccess);
type Contents = BTreeMap<Cell, BTreeSet<PointerView>>;

fn cells(
    pointers: &BTreeMap<VirValueId, BTreeSet<PointerView>>,
    value: VirValueId,
    offset: u64,
    access: VirMemoryAccess,
) -> Vec<Cell> {
    let Some(views) = pointers.get(&value) else {
        return Vec::new();
    };
    views
        .iter()
        .map(|p| {
            if p.field.is_some() || !p.offset.terms.is_empty() {
                return None;
            }
            Some((
                p.root,
                u64::try_from(p.offset.constant).ok()?.checked_add(offset)?,
                access,
            ))
        })
        .collect::<Option<Vec<_>>>()
        .unwrap_or_default()
}
fn read_cells(contents: &Contents, keys: Vec<Cell>) -> BTreeSet<PointerView> {
    // Every possible address must have known contents. Dropping an unknown
    // branch here would turn a partial source set into a false unique source.
    let mut result = BTreeSet::new();
    for key in keys {
        let Some(values) = contents.get(&key).filter(|v| !v.is_empty()) else {
            return BTreeSet::new();
        };
        result.extend(values.iter().cloned());
    }
    result
}

fn write_cells(contents: &mut Contents, keys: Vec<Cell>, values: &BTreeSet<PointerView>) -> bool {
    let mut changed = false;
    for key in keys {
        let entry = contents.entry(key).or_default();
        for value in values {
            if entry.len() == 4 {
                break;
            }
            changed |= entry.insert(value.clone());
        }
    }
    changed
}

type StoredResultView = (u32, u64, VirMemoryAccess, BTreeSet<PointerView>);

#[derive(Clone)]
enum Equation {
    PointerCopy(VirValueId, VirValueId),
    FieldTake(VirValueId, VirValueId, VirMemoryAccess),
    FieldStore(VirValueId, VirValueId, VirMemoryAccess),
    ObjectMove(VirValueId, VirValueId, VirMemoryAccess),
    PointerOffset(VirValueId, VirValueId, VirValueId),
    PointerConstantOffset(VirValueId, VirValueId, u64),
    PointerScaledOffset(VirValueId, VirValueId, VirValueId, u64),
    SlicePointer(VirValueId, VirValueId, VirValueId, VirValueId, u64),
    WordCopy(VirValueId, VirValueId),
    WordAdd(VirValueId, VirValueId, VirValueId),
    WordDifference(VirValueId, VirValueId, VirValueId),
    Call {
        // Independently reconstructed contents of indirect result buffers.
        // Roots here are physical callee input slots, never address guesses.
        stored_results: Option<Vec<StoredResultView>>,
        abi: Box<VirAbiSignature>,
        arguments: Vec<VirValueId>,
        results: Vec<VirValue>,
    },
}

#[cfg(test)]
pub(super) fn preserves_returned_view(
    function: &VirFunction,
    abi: &VirAbiSignature,
    memory: &VirMemorySchema,
) -> bool {
    preserves_closed_returned_view(
        function,
        abi,
        memory,
        &[],
        &VirAbiEnvironment::identity(&[]),
    )
}

pub(super) fn preserves_closed_returned_view(
    function: &VirFunction,
    abi: &VirAbiSignature,
    memory: &VirMemorySchema,
    functions: &[VirFunction],
    abis: &VirAbiEnvironment,
) -> bool {
    if !abi
        .results()
        .iter()
        .any(|b| b.interface().transfer.is_borrow())
    {
        return true;
    }
    if abi.borrow_result().is_none() && abi.borrow_result_alternatives().is_empty() {
        return false;
    }
    let Some(entry) = function.blocks.iter().find(|b| b.id == function.entry) else {
        return false;
    };
    let Some((pointers, words, _)) =
        infer_views(function, abi, memory, functions, abis, 0, &mut 4096)
    else {
        return false;
    };
    function.blocks.iter().all(|block| {
        let VirTerminator::Return { values } = &block.terminator.terminator else {
            return true;
        };
        abi.borrow_result()
            .into_iter()
            .chain(abi.borrow_result_alternatives().iter().map(|a| a.relation))
            .any(|relation| {
                returned_relation_matches(relation, abi, entry, values, &pointers, &words, memory)
            })
    })
}

type ViewFacts = (
    BTreeMap<VirValueId, BTreeSet<PointerView>>,
    BTreeMap<VirValueId, BTreeSet<Linear>>,
    Contents,
);

fn infer_views(
    function: &VirFunction,
    abi: &VirAbiSignature,
    memory: &VirMemorySchema,
    functions: &[VirFunction],
    abis: &VirAbiEnvironment,
    depth: usize,
    budget: &mut usize,
) -> Option<ViewFacts> {
    *budget = budget.checked_sub(1)?;
    if depth > 16 {
        return None;
    }
    let entry = function
        .blocks
        .iter()
        .find(|block| block.id == function.entry)?;
    let mut pointers = BTreeMap::<VirValueId, BTreeSet<PointerView>>::new();
    let mut words = BTreeMap::<VirValueId, BTreeSet<Linear>>::new();
    for value in &entry.parameters {
        match value.ty {
            VirType::Pointer { .. } => {
                pointers.insert(
                    value.id,
                    BTreeSet::from([PointerView {
                        root: value.id,
                        field: None,
                        offset: Linear::default(),
                        slice_length: None,
                    }]),
                );
            }
            VirType::U64 => {
                words.insert(value.id, BTreeSet::from([Linear::input(value.id)]));
            }
            VirType::Bool | VirType::Permission => {}
        }
    }
    let mut contents = Contents::new();
    let parameters = abi
        .parameters()
        .iter()
        .map(|b| b.value().access())
        .collect::<Option<Vec<_>>>()?;
    let fields = plan_parameter_reference_entries(memory, &parameters)?;
    for field in fields {
        let root = entry
            .parameters
            .get(field.pointer_slot as usize)
            .map(|p| p.id)?;
        contents.insert(
            (root, field.offset_bytes, field.reference),
            BTreeSet::from([PointerView {
                root,
                field: Some((field.offset_bytes, field.reference)),
                offset: Linear::default(),
                slice_length: None,
            }]),
        );
    }
    let mut equations = Vec::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            match &instruction.instruction {
                VirInstruction::LocalStorage { pointer_result, .. } => {
                    pointers.insert(
                        pointer_result.id,
                        BTreeSet::from([PointerView {
                            root: pointer_result.id,
                            field: None,
                            offset: Linear::default(),
                            slice_length: None,
                        }]),
                    );
                }
                VirInstruction::ResourceInitialize {
                    destination,
                    value,
                    access,
                    ..
                } if matches!(
                    memory.kind(access.ty),
                    Some(VirMemoryTypeKind::Pointer {
                        kind: VirPointerKind::Reference,
                        ..
                    })
                ) =>
                {
                    equations.push(Equation::FieldStore(*destination, *value, *access))
                }
                VirInstruction::ObjectTransfer {
                    destination,
                    source,
                    access,
                    ..
                } => equations.push(Equation::ObjectMove(*destination, *source, *access)),

                VirInstruction::Constant {
                    result,
                    value: VirConstant::U64(value),
                } => {
                    words.insert(result.id, BTreeSet::from([Linear::constant(*value)]));
                }
                VirInstruction::Load { result, .. } if result.ty == VirType::U64 => {
                    words.insert(result.id, BTreeSet::from([Linear::input(result.id)]));
                }
                VirInstruction::WordAdd {
                    result,
                    left,
                    right,
                } => equations.push(Equation::WordAdd(result.id, *left, *right)),
                VirInstruction::FieldAddress {
                    result,
                    base,
                    offset_bytes,
                    ..
                }
                | VirInstruction::TupleElementAddress {
                    result,
                    base,
                    offset_bytes,
                    ..
                }
                | VirInstruction::ObjectLeafAddress {
                    result,
                    base,
                    offset_bytes,
                    ..
                } => equations.push(Equation::PointerConstantOffset(
                    result.id,
                    *base,
                    *offset_bytes,
                )),
                VirInstruction::IndexAddress {
                    result,
                    base,
                    index,
                    stride_bytes,
                    ..
                } => equations.push(Equation::PointerScaledOffset(
                    result.id,
                    *base,
                    *index,
                    *stride_bytes,
                )),
                VirInstruction::SliceAddress {
                    pointer_result,
                    length_result,
                    base,
                    start,
                    end,
                    stride_bytes,
                    ..
                }
                | VirInstruction::SliceRange {
                    pointer_result,
                    length_result,
                    base,
                    start,
                    end,
                    stride_bytes,
                    ..
                } => {
                    equations.push(Equation::SlicePointer(
                        pointer_result.id,
                        *base,
                        *start,
                        *end,
                        *stride_bytes,
                    ));
                    equations.push(Equation::WordDifference(length_result.id, *end, *start));
                }
                VirInstruction::ResourceTake {
                    pointer_result,
                    source,
                    access,
                    ..
                } if matches!(
                    memory.kind(access.ty),
                    Some(VirMemoryTypeKind::Pointer {
                        kind: VirPointerKind::Reference,
                        ..
                    })
                ) =>
                {
                    equations.push(Equation::FieldTake(pointer_result.id, *source, *access))
                }
                VirInstruction::PointerOffset {
                    result,
                    base,
                    delta_bytes,
                } => equations.push(Equation::PointerOffset(result.id, *base, *delta_bytes)),
                VirInstruction::LoanBegin {
                    effect,
                    reference_result,
                    ..
                }
                | VirInstruction::LoanReborrow {
                    effect,
                    reference_result,
                    ..
                }
                | VirInstruction::LoanAliasShared {
                    effect,
                    reference_result,
                    ..
                } => equations.push(Equation::PointerCopy(
                    reference_result.id,
                    effect.source_pointer,
                )),
                VirInstruction::LoanAliasAuthority {
                    effect,
                    reference_result,
                    ..
                }
                | VirInstruction::LoanReborrowAuthority {
                    effect,
                    reference_result,
                    ..
                } => equations.push(Equation::PointerCopy(
                    reference_result.id,
                    effect.source_pointer,
                )),
                VirInstruction::Call {
                    target,
                    arguments,
                    results,
                } => {
                    // Opaque scalar results are fresh values, not entry aliases.
                    // Slice lengths are supplied by the paired call equation.
                    let slice_length = target
                        .abi
                        .as_ref()
                        .and_then(|abi| abi.results().first())
                        .filter(|binding| matches!(binding.value(), VirAbiValue::Slice { .. }))
                        .and_then(|binding| binding.result_slots().get(1))
                        .copied();
                    for (index, result) in results.iter().enumerate() {
                        if result.ty == VirType::U64 && slice_length != Some(index as u32) {
                            words.insert(result.id, BTreeSet::from([Linear::input(result.id)]));
                        }
                    }
                    if let Some(call_abi) = &target.abi {
                        let stored_results = call_stored_views(
                            target,
                            call_abi,
                            memory,
                            functions,
                            abis,
                            depth + 1,
                            budget,
                        );
                        equations.push(Equation::Call {
                            stored_results,
                            abi: Box::new(call_abi.clone()),
                            arguments: arguments.clone(),
                            results: results.clone(),
                        });
                    }
                }
                _ => {}
            }
        }
        let targets = match &block.terminator.terminator {
            VirTerminator::Jump { target } => vec![target],
            VirTerminator::Branch {
                then_target,
                else_target,
                ..
            } => vec![then_target, else_target],
            VirTerminator::Return { .. } => Vec::new(),
        };
        for target in targets {
            let destination = function
                .blocks
                .iter()
                .find(|block| block.id == target.block)?;
            for (parameter, argument) in destination.parameters.iter().zip(&target.arguments) {
                match parameter.ty {
                    VirType::Pointer { .. } => {
                        equations.push(Equation::PointerCopy(parameter.id, *argument))
                    }
                    VirType::U64 => equations.push(Equation::WordCopy(parameter.id, *argument)),
                    VirType::Bool | VirType::Permission => {}
                }
            }
        }
    }
    for _ in 0..=equations.len().saturating_mul(4) {
        let changed = equations.iter().fold(false, |changed, equation| {
            apply_equation(equation, &mut pointers, &mut words, &mut contents, memory) | changed
        });
        if !changed {
            if equations.iter().any(|e| match e {
                Equation::FieldStore(destination, value, access) => {
                    cells(&pointers, *destination, 0, *access).is_empty()
                        || pointers.get(value).is_none_or(BTreeSet::is_empty)
                }
                Equation::ObjectMove(destination, source, access) => {
                    memory.object_shape(*access).map_or(true, |shape| {
                        shape
                            .resource_leaves()
                            .iter()
                            .filter(|l| l.kind() == VirPointerKind::Reference)
                            .any(|leaf| {
                                cells(
                                    &pointers,
                                    *destination,
                                    leaf.bytes().start_bytes(),
                                    leaf.access(),
                                )
                                .is_empty()
                                    || read_cells(
                                        &contents,
                                        cells(
                                            &pointers,
                                            *source,
                                            leaf.bytes().start_bytes(),
                                            leaf.access(),
                                        ),
                                    )
                                    .is_empty()
                            })
                    })
                }
                Equation::Call { stored_results, .. } => stored_results.is_none(),
                _ => false,
            }) {
                return None;
            }
            return Some((pointers, words, contents));
        }
    }
    None
}

/// Trace result-buffer leaves through the closed callee's instructions. The
/// ABI alone makes no claim about which input field a stored output contains.
fn call_stored_views(
    target: &VirCallTarget,
    abi: &VirAbiSignature,
    memory: &VirMemorySchema,
    functions: &[VirFunction],
    abis: &VirAbiEnvironment,
    depth: usize,
    budget: &mut usize,
) -> Option<Vec<StoredResultView>> {
    let mut leaves = Vec::new();
    for binding in abi.results() {
        if !binding.value().is_indirect_aggregate() {
            continue;
        }
        let shape = memory.object_shape(binding.value().access()?).ok()?;
        for leaf in shape
            .resource_leaves()
            .iter()
            .filter(|l| l.kind() == VirPointerKind::Reference)
        {
            leaves.push((
                *binding.parameter_slots().first()?,
                leaf.bytes().start_bytes(),
                leaf.access(),
            ));
        }
    }
    if leaves.is_empty() {
        return Some(Vec::new());
    }
    let callee = functions.iter().find(|f| f.name == target.symbol)?;
    let declared = &abis.function(callee.id)?.signature;
    if declared != abi {
        return None;
    }
    let entry = callee.blocks.iter().find(|b| b.id == callee.entry)?;
    let (pointers, _, contents) = infer_views(callee, abi, memory, functions, abis, depth, budget)?;
    leaves
        .into_iter()
        .map(|(slot, offset, access)| {
            let pointer = entry.parameters.get(slot as usize)?.id;
            let facts = read_cells(&contents, cells(&pointers, pointer, offset, access));
            if facts.is_empty() {
                return None;
            }
            let mapped = facts
                .into_iter()
                .map(|mut view| {
                    if !view.offset.terms.is_empty() || view.slice_length.is_some() {
                        return None;
                    }
                    let source_slot = entry.parameters.iter().position(|p| p.id == view.root)?;
                    view.root = VirValueId::new(u32::try_from(source_slot).ok()?);
                    Some(view)
                })
                .collect::<Option<BTreeSet<_>>>()?;
            Some((slot, offset, access, mapped))
        })
        .collect()
}

fn apply_equation(
    equation: &Equation,
    pointers: &mut BTreeMap<VirValueId, BTreeSet<PointerView>>,
    words: &mut BTreeMap<VirValueId, BTreeSet<Linear>>,
    contents: &mut Contents,
    memory: &VirMemorySchema,
) -> bool {
    match equation {
        Equation::FieldTake(result, source, reference) => {
            let facts = read_cells(contents, cells(pointers, *source, 0, *reference));
            extend(pointers, *result, facts)
        }
        Equation::FieldStore(destination, value, reference) => {
            let facts = pointers.get(value).cloned().unwrap_or_default();
            write_cells(
                contents,
                cells(pointers, *destination, 0, *reference),
                &facts,
            )
        }
        Equation::ObjectMove(destination, source, access) => {
            let Ok(shape) = memory.object_shape(*access) else {
                return false;
            };
            let mut changed = false;
            for leaf in shape
                .resource_leaves()
                .iter()
                .filter(|l| l.kind() == VirPointerKind::Reference)
            {
                let facts = read_cells(
                    contents,
                    cells(pointers, *source, leaf.bytes().start_bytes(), leaf.access()),
                );
                changed |= write_cells(
                    contents,
                    cells(
                        pointers,
                        *destination,
                        leaf.bytes().start_bytes(),
                        leaf.access(),
                    ),
                    &facts,
                );
            }
            changed
        }
        Equation::PointerCopy(result, source) => extend(
            pointers,
            *result,
            pointers.get(source).cloned().unwrap_or_default(),
        ),
        Equation::PointerConstantOffset(result, base, offset) => {
            let offset = Linear::constant(*offset);
            let facts = pointers
                .get(base)
                .into_iter()
                .flatten()
                .filter_map(|pointer| {
                    Some(PointerView {
                        root: pointer.root,
                        field: pointer.field,
                        offset: pointer.offset.add(&offset)?,
                        slice_length: None,
                    })
                })
                .collect();
            extend(pointers, *result, facts)
        }
        Equation::PointerScaledOffset(result, base, index, stride) => {
            let facts = pointers
                .get(base)
                .into_iter()
                .flatten()
                .flat_map(|pointer| {
                    words
                        .get(index)
                        .into_iter()
                        .flatten()
                        .filter_map(move |index| {
                            Some(PointerView {
                                root: pointer.root,
                                field: pointer.field,
                                offset: pointer.offset.add(&index.scale(*stride)?)?,
                                slice_length: None,
                            })
                        })
                })
                .collect();
            extend(pointers, *result, facts)
        }
        Equation::SlicePointer(result, base, start, end, stride) => {
            let mut facts = BTreeSet::new();
            for pointer in pointers.get(base).into_iter().flatten() {
                for start in words.get(start).into_iter().flatten() {
                    for end in words.get(end).into_iter().flatten() {
                        if let Some((offset, length)) = start
                            .scale(*stride)
                            .and_then(|delta| pointer.offset.add(&delta))
                            .zip(end.sub(start))
                        {
                            facts.insert(PointerView {
                                root: pointer.root,
                                field: pointer.field,
                                offset,
                                slice_length: Some(length),
                            });
                        }
                    }
                }
            }
            extend(pointers, *result, facts)
        }
        Equation::PointerOffset(result, base, delta) => {
            let facts = pointers
                .get(base)
                .into_iter()
                .flatten()
                .flat_map(|pointer| {
                    words
                        .get(delta)
                        .into_iter()
                        .flatten()
                        .filter_map(move |delta| {
                            Some(PointerView {
                                root: pointer.root,
                                field: pointer.field,
                                offset: pointer.offset.add(delta)?,
                                slice_length: None,
                            })
                        })
                })
                .collect();
            extend(pointers, *result, facts)
        }
        Equation::WordCopy(result, source) => extend(
            words,
            *result,
            words.get(source).cloned().unwrap_or_default(),
        ),
        Equation::WordAdd(result, left, right) => {
            let facts = words
                .get(left)
                .into_iter()
                .flatten()
                .flat_map(|left| {
                    words
                        .get(right)
                        .into_iter()
                        .flatten()
                        .filter_map(move |right| left.add(right))
                })
                .collect();
            extend(words, *result, facts)
        }
        Equation::WordDifference(result, end, start) => {
            let facts = words
                .get(end)
                .into_iter()
                .flatten()
                .flat_map(|end| {
                    words
                        .get(start)
                        .into_iter()
                        .flatten()
                        .filter_map(move |start| end.sub(start))
                })
                .collect();
            extend(words, *result, facts)
        }
        Equation::Call {
            stored_results,
            abi,
            arguments,
            results,
        } => {
            let mut changed = false;
            for (destination_slot, offset, access, formal) in stored_results.iter().flatten() {
                let Some(destination) = arguments.get(*destination_slot as usize) else {
                    continue;
                };
                let mut facts = BTreeSet::new();
                for source in formal {
                    let Some(argument) = arguments.get(source.root.get() as usize) else {
                        continue;
                    };
                    let actual = if let Some((offset, access)) = source.field {
                        read_cells(contents, cells(pointers, *argument, offset, access))
                    } else {
                        pointers.get(argument).cloned().unwrap_or_default()
                    };
                    for mut view in actual {
                        if let Some(offset) = view.offset.add(&source.offset) {
                            view.offset = offset;
                            facts.insert(view);
                        }
                    }
                }
                changed |= write_cells(
                    contents,
                    cells(pointers, *destination, *offset, *access),
                    &facts,
                );
            }
            for relation in abi
                .borrow_result()
                .into_iter()
                .chain(abi.borrow_result_alternatives().iter().map(|a| a.relation))
            {
                let (Some(source), Some(result)) = (
                    abi.parameters().get(relation.parameter as usize),
                    abi.results().get(relation.result as usize),
                ) else {
                    continue;
                };
                let (Some(&source_pointer), Some(result_pointer)) = (
                    source
                        .parameter_slots()
                        .first()
                        .and_then(|slot| arguments.get(*slot as usize)),
                    result
                        .result_slots()
                        .first()
                        .and_then(|slot| results.get(*slot as usize))
                        .map(|value| value.id),
                ) else {
                    continue;
                };
                if relation.parameter_field.is_some() {
                    let Some(entry) = field_source_plan(memory, abi, relation) else {
                        continue;
                    };
                    let facts = read_cells(
                        contents,
                        cells(
                            pointers,
                            source_pointer,
                            entry.offset_bytes,
                            entry.reference,
                        ),
                    );
                    changed |= extend(pointers, result_pointer, facts);
                    continue;
                }
                let dynamic_offset = matches!(
                    relation.projection,
                    crate::BorrowProjection::ArraySlice {
                        start: crate::BorrowSliceBound::ReturnedOffset,
                        ..
                    }
                );
                let projection = if dynamic_offset {
                    Some((Linear::input(result_pointer), None))
                } else {
                    projection_expressions(relation.projection, abi, arguments, source, words)
                };
                if let Some((offset, length)) = projection {
                    let length = if matches!(
                        relation.projection,
                        crate::BorrowProjection::ArraySlice {
                            end: crate::BorrowSliceBound::ReturnedLength,
                            ..
                        }
                    ) {
                        result
                            .result_slots()
                            .get(1)
                            .and_then(|slot| results.get(*slot as usize))
                            .map(|v| Linear::input(v.id))
                    } else {
                        length
                    };
                    let facts = pointers
                        .get(&source_pointer)
                        .into_iter()
                        .flatten()
                        .filter_map(|pointer| {
                            Some(PointerView {
                                root: pointer.root,
                                field: pointer.field,
                                offset: pointer.offset.add(&offset)?,
                                slice_length: length.clone(),
                            })
                        })
                        .collect();
                    changed |= extend(pointers, result_pointer, facts);
                    if let (Some(length), Some(&slot)) = (length, result.result_slots().get(1))
                        && abi.physical().results.get(slot as usize) == Some(&VirType::U64)
                    {
                        changed |=
                            extend(words, results[slot as usize].id, BTreeSet::from([length]));
                    }
                }
            }
            changed
        }
    }
}

fn projection_expressions(
    projection: crate::BorrowProjection,
    abi: &VirAbiSignature,
    arguments: &[VirValueId],
    source: &VirAbiBinding,
    words: &BTreeMap<VirValueId, BTreeSet<Linear>>,
) -> Option<(Linear, Option<Linear>)> {
    match projection {
        crate::BorrowProjection::Whole => {
            let length = source
                .parameter_slots()
                .get(1)
                .and_then(|slot| singleton(words.get(arguments.get(*slot as usize)?)));
            Some((Linear::default(), length))
        }
        crate::BorrowProjection::Fixed { offset_bytes, .. } => {
            Some((Linear::constant(offset_bytes), None))
        }
        crate::BorrowProjection::ArraySlice {
            start,
            end: crate::BorrowSliceBound::ReturnedLength,
            offset_bytes,
            stride_bytes,
            ..
        } => Some((
            bound_expression(start, abi, arguments, source, words)?
                .scale(u64::from(stride_bytes))?
                .add(&Linear::constant(u64::from(offset_bytes)))?,
            None,
        )),
        crate::BorrowProjection::Slice { start, end, .. }
        | crate::BorrowProjection::ArraySlice { start, end, .. } => {
            let stride_bytes = projection.slice_stride().expect("slice projection");
            let bound = |b| {
                if b == crate::BorrowSliceBound::SourceLength
                    && let Some(length) = projection.array_length()
                {
                    Some(Linear::constant(length))
                } else {
                    bound_expression(b, abi, arguments, source, words)
                }
            };
            let start = bound(start)?;
            let end = bound(end)?;
            Some((
                start
                    .scale(stride_bytes)?
                    .add(&Linear::constant(projection.array_offset()))?,
                Some(end.sub(&start)?),
            ))
        }
    }
}

fn bound_expression(
    bound: crate::BorrowSliceBound,
    abi: &VirAbiSignature,
    arguments: &[VirValueId],
    source: &VirAbiBinding,
    words: &BTreeMap<VirValueId, BTreeSet<Linear>>,
) -> Option<Linear> {
    let value = match bound {
        crate::BorrowSliceBound::ReturnedLength | crate::BorrowSliceBound::ReturnedOffset => {
            return None;
        }
        crate::BorrowSliceBound::Constant(value) => return Some(Linear::constant(value)),
        crate::BorrowSliceBound::Parameter(parameter) => {
            let binding = abi.parameters().get(parameter as usize)?;
            *arguments.get(*binding.parameter_slots().first()? as usize)?
        }
        crate::BorrowSliceBound::SourceLength => {
            *arguments.get(*source.parameter_slots().get(1)? as usize)?
        }
    };
    singleton(words.get(&value))
}

fn returned_relation_matches(
    relation: crate::BorrowResultRelation,
    abi: &VirAbiSignature,
    entry: &VirBasicBlock,
    values: &[VirValueId],
    pointers: &BTreeMap<VirValueId, BTreeSet<PointerView>>,
    words: &BTreeMap<VirValueId, BTreeSet<Linear>>,
    memory: &VirMemorySchema,
) -> bool {
    let (Some(source), Some(result)) = (
        abi.parameters().get(relation.parameter as usize),
        abi.results().get(relation.result as usize),
    ) else {
        return false;
    };
    let (Some(source_pointer), Some(result_pointer)) = (
        source
            .parameter_slots()
            .first()
            .and_then(|slot| entry.parameters.get(*slot as usize)),
        result
            .result_slots()
            .first()
            .and_then(|slot| values.get(*slot as usize)),
    ) else {
        return false;
    };
    let entry_arguments = entry
        .parameters
        .iter()
        .map(|value| value.id)
        .collect::<Vec<_>>();
    let dynamic_offset = matches!(
        relation.projection,
        crate::BorrowProjection::ArraySlice {
            start: crate::BorrowSliceBound::ReturnedOffset,
            end: crate::BorrowSliceBound::ReturnedLength,
            ..
        }
    );
    let projection = if dynamic_offset {
        Some((Linear::default(), None))
    } else {
        projection_expressions(relation.projection, abi, &entry_arguments, source, words)
    };
    let Some((offset, length)) = projection else {
        return false;
    };
    let Some(actual) = singleton(pointers.get(result_pointer)) else {
        return false;
    };
    let expected_field = if relation.parameter_field.is_some() {
        let Some(entry) = field_source_plan(memory, abi, relation) else {
            return false;
        };
        Some((entry.offset_bytes, entry.reference))
    } else {
        None
    };
    if actual.field != expected_field
        || actual.root != source_pointer.id
        || (!dynamic_offset && actual.offset != offset)
    {
        return false;
    }
    let length = if matches!(
        relation.projection,
        crate::BorrowProjection::ArraySlice {
            end: crate::BorrowSliceBound::ReturnedLength,
            ..
        }
    ) {
        let Some(paired_length) = actual.slice_length else {
            return false;
        };
        Some(paired_length)
    } else {
        length
    };
    if let Some(expected) = length {
        let Some(result_length) = result
            .result_slots()
            .get(1)
            .and_then(|slot| values.get(*slot as usize))
        else {
            return false;
        };
        if words.get(result_length) != Some(&BTreeSet::from([expected])) {
            return false;
        }
    }
    true
}

fn singleton<T: Clone + Ord>(values: Option<&BTreeSet<T>>) -> Option<T> {
    let values = values?;
    (values.len() == 1).then(|| values.first().unwrap().clone())
}

fn extend<T: Ord>(
    facts: &mut BTreeMap<VirValueId, BTreeSet<T>>,
    result: VirValueId,
    additions: BTreeSet<T>,
) -> bool {
    let current = facts.entry(result).or_default();
    if current.len() >= 4 {
        return false;
    }
    let mut changed = false;
    for addition in additions.into_iter().take(4 - current.len()) {
        changed |= current.insert(addition);
    }
    changed
}

fn field_source_plan(
    memory: &VirMemorySchema,
    abi: &VirAbiSignature,
    relation: crate::BorrowResultRelation,
) -> Option<ParameterReferenceEntry> {
    let parameters = abi
        .parameters()
        .iter()
        .map(|b| b.value().access())
        .collect::<Option<Vec<_>>>()?;
    let results = abi
        .results()
        .iter()
        .map(|b| b.value().access())
        .collect::<Option<Vec<_>>>()?;
    plan_parameter_field_result(memory, &parameters, &results, relation)
}

#[cfg(test)]
mod field_tests {
    use super::*;

    #[test]
    fn field_sources_keep_root_leaf_and_referent_offsets_separate() {
        let memory = VirMemorySchema::core_u64();
        // The equation engine treats accesses as canonical opaque identities;
        // instruction validation separately requires a real reference type.
        let reference = VirMemoryAccess::core_u64();
        let a = VirValueId::new(0);
        let b = VirValueId::new(1);
        let address = VirValueId::new(2);
        let result = VirValueId::new(3);
        let other = VirValueId::new(4);
        let alias = VirValueId::new(5);
        let mut pointers = [a, b]
            .into_iter()
            .map(|id| {
                (
                    id,
                    BTreeSet::from([PointerView {
                        root: id,
                        field: None,
                        offset: Linear::default(),
                        slice_length: None,
                    }]),
                )
            })
            .collect();
        let mut words = BTreeMap::new();
        let mut contents = Contents::new();
        for (root, offset) in [(a, 8), (b, 0)] {
            contents.insert(
                (root, offset, reference),
                BTreeSet::from([PointerView {
                    root,
                    field: Some((offset, reference)),
                    offset: Linear::default(),
                    slice_length: None,
                }]),
            );
        }
        for equation in [
            Equation::PointerConstantOffset(address, a, 8),
            Equation::FieldTake(result, address, reference),
            Equation::FieldTake(other, b, reference),
            Equation::PointerCopy(alias, result),
        ] {
            assert!(apply_equation(
                &equation,
                &mut pointers,
                &mut words,
                &mut contents,
                &memory
            ));
        }
        assert_eq!(
            singleton(pointers.get(&result)),
            Some(PointerView {
                root: a,
                field: Some((8, reference)),
                offset: Linear::default(),
                slice_length: None,
            })
        );
        assert_ne!(pointers.get(&result), pointers.get(&other));
        assert_eq!(pointers.get(&result), pointers.get(&alias));
        // Following a pointer or using an unknown offset must not invent a field.
        assert!(!apply_equation(
            &Equation::FieldTake(VirValueId::new(6), result, reference),
            &mut pointers,
            &mut words,
            &mut contents,
            &memory
        ));
        pointers.insert(
            address,
            BTreeSet::from([PointerView {
                root: a,
                field: None,
                offset: Linear::input(VirValueId::new(7)),
                slice_length: None,
            }]),
        );
        assert!(!apply_equation(
            &Equation::FieldTake(VirValueId::new(8), address, reference),
            &mut pointers,
            &mut words,
            &mut contents,
            &memory
        ));
    }
}
