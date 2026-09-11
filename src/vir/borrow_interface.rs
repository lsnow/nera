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
    offset: Linear,
}

#[derive(Clone)]
enum Equation {
    PointerCopy(VirValueId, VirValueId),
    PointerOffset(VirValueId, VirValueId, VirValueId),
    PointerConstantOffset(VirValueId, VirValueId, u64),
    PointerScaledOffset(VirValueId, VirValueId, VirValueId, u64),
    WordCopy(VirValueId, VirValueId),
    WordAdd(VirValueId, VirValueId, VirValueId),
    WordDifference(VirValueId, VirValueId, VirValueId),
    Call {
        abi: Box<VirAbiSignature>,
        arguments: Vec<VirValueId>,
        results: Vec<VirValue>,
    },
}

pub(super) fn preserves_returned_view(function: &VirFunction, abi: &VirAbiSignature) -> bool {
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
    let Some(entry) = function
        .blocks
        .iter()
        .find(|block| block.id == function.entry)
    else {
        return false;
    };
    let mut pointers = BTreeMap::<VirValueId, BTreeSet<PointerView>>::new();
    let mut words = BTreeMap::<VirValueId, BTreeSet<Linear>>::new();
    for value in &entry.parameters {
        match value.ty {
            VirType::Pointer { .. } => {
                pointers.insert(
                    value.id,
                    BTreeSet::from([PointerView {
                        root: value.id,
                        offset: Linear::default(),
                    }]),
                );
            }
            VirType::U64 => {
                words.insert(value.id, BTreeSet::from([Linear::input(value.id)]));
            }
            VirType::Bool | VirType::Permission => {}
        }
    }
    let mut equations = Vec::new();
    for block in &function.blocks {
        for instruction in &block.instructions {
            match &instruction.instruction {
                VirInstruction::Constant {
                    result,
                    value: VirConstant::U64(value),
                } => {
                    words.insert(result.id, BTreeSet::from([Linear::constant(*value)]));
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
                    equations.push(Equation::PointerScaledOffset(
                        pointer_result.id,
                        *base,
                        *start,
                        *stride_bytes,
                    ));
                    equations.push(Equation::WordDifference(length_result.id, *end, *start));
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
                    if let Some(call_abi) = &target.abi {
                        equations.push(Equation::Call {
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
            let Some(destination) = function
                .blocks
                .iter()
                .find(|block| block.id == target.block)
            else {
                return false;
            };
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
            apply_equation(equation, &mut pointers, &mut words) | changed
        });
        if !changed {
            return function.blocks.iter().all(|block| {
                let VirTerminator::Return { values } = &block.terminator.terminator else {
                    return true;
                };
                abi.borrow_result()
                    .into_iter()
                    .chain(abi.borrow_result_alternatives().iter().map(|a| a.relation))
                    .any(|relation| {
                        returned_relation_matches(relation, abi, entry, values, &pointers, &words)
                    })
            });
        }
    }
    false
}

fn apply_equation(
    equation: &Equation,
    pointers: &mut BTreeMap<VirValueId, BTreeSet<PointerView>>,
    words: &mut BTreeMap<VirValueId, BTreeSet<Linear>>,
) -> bool {
    match equation {
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
                        offset: pointer.offset.add(&offset)?,
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
                                offset: pointer.offset.add(&index.scale(*stride)?)?,
                            })
                        })
                })
                .collect();
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
                                offset: pointer.offset.add(delta)?,
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
            abi,
            arguments,
            results,
        } => {
            let mut changed = false;
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
                if let Some((offset, length)) =
                    projection_expressions(relation.projection, abi, arguments, source, words)
                {
                    let facts = pointers
                        .get(&source_pointer)
                        .into_iter()
                        .flatten()
                        .filter_map(|pointer| {
                            Some(PointerView {
                                root: pointer.root,
                                offset: pointer.offset.add(&offset)?,
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
        crate::BorrowProjection::Slice {
            start,
            end,
            stride_bytes,
            ..
        } => {
            let start = bound_expression(start, abi, arguments, source, words)?;
            let end = bound_expression(end, abi, arguments, source, words)?;
            Some((start.scale(stride_bytes)?, Some(end.sub(&start)?)))
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
    let Some((offset, length)) =
        projection_expressions(relation.projection, abi, &entry_arguments, source, words)
    else {
        return false;
    };
    let expected = PointerView {
        root: source_pointer.id,
        offset,
    };
    if pointers.get(result_pointer) != Some(&BTreeSet::from([expected])) {
        return false;
    }
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
