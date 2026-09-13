//! Conservative post-CFG non-lexical loan-end planning.
//!
//! Each block is planned independently after the complete CFG has been built.
//! Authorities defined and consumed in one block can therefore end after
//! their local last use even in a branching function. Authorities carried by
//! block parameters or terminators keep their lexical end: moving those ends
//! requires edge-specific authority reconstruction and must never be guessed.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet};

use super::draft::{
    DraftBlock, DraftInstruction, DraftRegionConstraint, PendingEffect, PendingLoanEnd,
};
use crate::vir::{
    VirBlockId, VirFunctionId, VirInstruction, VirLoanId, VirLocation, VirSourceMapEntry,
    VirValueId,
};

const MAX_REGION_RELATIONS: usize = 4_096;
const MAX_PARENT_DEPTH: usize = 512;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LoanEndPlanningError {
    RegionRelationBudget,
    CyclicRegionConstraints,
    MissingRegionInclusion { loan: VirLoanId, parent: VirLoanId },
    UnexpectedPendingEffect,
    EndBeforeLastUse(Option<VirLoanId>),
    InvalidParentGraph(VirLoanId),
    MissingSourceLocation { block: VirBlockId, ordinal: u64 },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) struct LoanEndPlanSummary {
    pub(super) ends: usize,
    pub(super) moved: usize,
    pub(super) lexical_fallbacks: usize,
}

#[derive(Clone, Debug)]
struct IndexedInstruction {
    old_ordinal: usize,
    instruction: DraftInstruction,
}

#[derive(Clone, Debug)]
struct PlannedEnd {
    old_ordinal: usize,
    effect: PendingLoanEnd,
    lexical_boundary: usize,
    planned_boundary: usize,
    movable: bool,
    depth: usize,
}

/// Moves eligible pending `LoanEnd` effects to the first boundary after their
/// final authority use, then rewrites source-map instruction identities.
pub(super) fn plan_with_specs(
    function: VirFunctionId,
    constraints: &[DraftRegionConstraint],
    blocks: &mut [DraftBlock],
    source_map_entries: &mut [VirSourceMapEntry],
    local_specs: &mut [super::local_spec::LocalSpec],
) -> Result<LoanEndPlanSummary, LoanEndPlanningError> {
    let regions = RegionSolution::solve(constraints)?;
    let parents = collect_and_check_parents(blocks, &regions)?;
    let mut summary = LoanEndPlanSummary::default();
    let mut remapped = BTreeMap::new();

    for block in blocks {
        // Anchor before the next non-movable operation. Ends moved across this
        // boundary are observed in their final order without making Spec a use.
        let following: Vec<_> = local_specs
            .iter()
            .enumerate()
            .filter(|(_, s)| s.block == block.id)
            .map(|(index, s)| {
                (
                    index,
                    block
                        .instructions
                        .iter()
                        .enumerate()
                        .skip(s.boundary)
                        .find(|(_, i)| {
                            !matches!(i, DraftInstruction::Pending(PendingEffect::LoanEnd(_)))
                        })
                        .map(|(ordinal, _)| ordinal as u64),
                )
            })
            .collect();
        let block_summary = plan_block(block, &parents, &mut remapped)?;
        for (index, next) in following {
            local_specs[index].boundary = if let Some(ordinal) = next {
                *remapped.get(&(block.id, ordinal)).ok_or(
                    LoanEndPlanningError::MissingSourceLocation {
                        block: block.id,
                        ordinal,
                    },
                )? as usize
            } else {
                block.instructions.len()
            };
        }
        summary.ends += block_summary.ends;
        summary.moved += block_summary.moved;
        summary.lexical_fallbacks += block_summary.lexical_fallbacks;
    }
    remap_source_locations(function, source_map_entries, &remapped)?;
    Ok(summary)
}

fn plan_block(
    block: &mut DraftBlock,
    parents: &BTreeMap<VirLoanId, VirLoanId>,
    remapped: &mut BTreeMap<(VirBlockId, u64), u64>,
) -> Result<LoanEndPlanSummary, LoanEndPlanningError> {
    let old = std::mem::take(&mut block.instructions);
    let mut retained = Vec::new();
    let mut ends = Vec::new();
    for (old_ordinal, instruction) in old.into_iter().enumerate() {
        match instruction {
            DraftInstruction::Pending(PendingEffect::LoanEnd(effect)) => {
                ends.push(PlannedEnd {
                    old_ordinal,
                    effect,
                    lexical_boundary: retained.len(),
                    planned_boundary: retained.len(),
                    movable: true,
                    depth: 0,
                });
            }
            DraftInstruction::Pending(_) => {
                return Err(LoanEndPlanningError::UnexpectedPendingEffect);
            }
            instruction @ DraftInstruction::Canonical(_) => retained.push(IndexedInstruction {
                old_ordinal,
                instruction,
            }),
        }
    }

    if ends.is_empty() {
        for (new_ordinal, instruction) in retained.into_iter().enumerate() {
            remapped.insert(
                (block.id, instruction.old_ordinal as u64),
                new_ordinal as u64,
            );
            block.instructions.push(instruction.instruction);
        }
        return Ok(LoanEndPlanSummary::default());
    }

    let mut definitions = BTreeMap::new();
    for (index, instruction) in retained.iter().enumerate() {
        let DraftInstruction::Canonical(instruction) = &instruction.instruction else {
            unreachable!("retained instructions are canonical");
        };
        instruction
            .instruction
            .visit_results(|result| _ = definitions.insert(result.id, index + 1));
    }

    let terminator = block
        .terminator
        .as_ref()
        .ok_or(LoanEndPlanningError::UnexpectedPendingEffect)?;
    for end in &mut ends {
        end.depth = end
            .effect
            .effect
            .loan()
            .map_or(Ok(0), |loan| loan_depth(loan, parents))?;
        if !end.movable {
            continue;
        }
        let authority = [
            end.effect.effect.source_pointer(),
            end.effect.effect.source_permission(),
        ];
        let Some(definition_boundary) = authority
            .into_iter()
            .filter_map(|value| definitions.get(&value).copied())
            .max()
        else {
            // Block parameters and future ABI-provided reference authorities
            // have no local instruction definition. Their lexical end is a
            // safe upper bound; guessing a shorter boundary is not.
            end.movable = false;
            continue;
        };
        let mut last_use = definition_boundary;
        for (index, instruction) in retained.iter().enumerate() {
            let DraftInstruction::Canonical(instruction) = &instruction.instruction else {
                unreachable!("retained instructions are canonical");
            };
            let mut used = false;
            instruction.instruction.visit_operands(|operand| {
                used |= authority.contains(&operand);
            });
            if used {
                last_use = last_use.max(index + 1);
                if instruction_escapes_authority(&instruction.instruction, &authority) {
                    end.movable = false;
                }
            }
        }
        terminator.terminator.visit_operands(|operand| {
            if authority.contains(&operand) {
                end.movable = false;
            }
        });
        if last_use > end.lexical_boundary {
            return Err(LoanEndPlanningError::EndBeforeLastUse(
                end.effect.effect.loan(),
            ));
        }
        if end.movable {
            end.planned_boundary = last_use;
        }
    }

    // Every authority of every child loan must end before any authority of
    // its parent. Loan IDs are dense and parents precede children, but the
    // fixed point also rejects malformed or unexpectedly deep graphs.
    for _ in 0..=MAX_PARENT_DEPTH {
        let boundaries = ends
            .iter()
            .filter_map(|end| {
                end.effect
                    .effect
                    .loan()
                    .map(|loan| (loan, end.planned_boundary))
            })
            .fold(
                BTreeMap::<_, usize>::new(),
                |mut result, (loan, boundary)| {
                    result
                        .entry(loan)
                        .and_modify(|current| *current = (*current).max(boundary))
                        .or_insert(boundary);
                    result
                },
            );
        let mut changed = false;
        for end in &mut ends {
            let required = parents
                .iter()
                .filter(|(_, parent)| Some(**parent) == end.effect.effect.loan())
                .filter_map(|(child, _)| boundaries.get(child))
                .copied()
                .max()
                .unwrap_or(0);
            let planned = end.planned_boundary.max(required);
            if planned > end.lexical_boundary {
                return Err(LoanEndPlanningError::InvalidParentGraph(
                    end.effect.effect.loan().unwrap_or(VirLoanId::new(u32::MAX)),
                ));
            }
            changed |= planned != end.planned_boundary;
            end.planned_boundary = planned;
        }
        if !changed {
            break;
        }
    }

    ends.sort_by_key(|end| (end.planned_boundary, Reverse(end.depth), end.old_ordinal));
    let summary = LoanEndPlanSummary {
        ends: ends.len(),
        moved: ends
            .iter()
            .filter(|end| end.planned_boundary < end.lexical_boundary)
            .count(),
        lexical_fallbacks: ends.iter().filter(|end| !end.movable).count(),
    };

    let mut retained = retained.into_iter().peekable();
    let mut ends = ends.into_iter().peekable();
    for boundary in 0.. {
        while ends
            .peek()
            .is_some_and(|end| end.planned_boundary == boundary)
        {
            let end = ends.next().expect("peeked end exists");
            let new_ordinal = block.instructions.len() as u64;
            remapped.insert((block.id, end.old_ordinal as u64), new_ordinal);
            block
                .instructions
                .push(DraftInstruction::Pending(PendingEffect::LoanEnd(
                    end.effect,
                )));
        }
        let Some(instruction) = retained.next() else {
            break;
        };
        let new_ordinal = block.instructions.len() as u64;
        remapped.insert((block.id, instruction.old_ordinal as u64), new_ordinal);
        block.instructions.push(instruction.instruction);
    }
    if ends.next().is_some() {
        return Err(LoanEndPlanningError::UnexpectedPendingEffect);
    }
    Ok(summary)
}

fn instruction_escapes_authority(
    instruction: &VirInstruction,
    authority: &[VirValueId; 2],
) -> bool {
    match instruction {
        // A runtime-selected parent has no static graph edge here. Retain
        // its lexical end; child ends remain before it in reverse scope order.
        VirInstruction::LoanReborrowAuthority { effect, .. } => {
            authority.contains(&effect.source_permission)
        }
        VirInstruction::Call {
            arguments,
            results,
            target,
        } => {
            // A signature-bound borrow with an explicit restoration result is
            // a local use, not an escape. Tie that result to the exact token
            // being ended; unknown/escaping/multi-call token chains retain the
            // lexical fallback. The verifier independently checks the ABI and
            // the returned authority before this end can discharge a loan.
            arguments.iter().enumerate().any(|(slot, argument)| {
                authority.contains(argument)
                    && !target.abi.as_ref().is_some_and(|abi| {
                        abi.parameters().iter().enumerate().any(|(index, binding)| {
                            binding.interface().transfer.is_borrow()
                                && abi.borrow_result_parameter() != Some(index)
                                && binding
                                    .parameter_slots()
                                    .iter()
                                    .any(|bound| *bound as usize == slot)
                                && binding
                                    .parameter_slots()
                                    .first()
                                    .and_then(|slot| arguments.get(*slot as usize))
                                    == Some(&authority[0])
                                && binding.result_slots().len() == 1
                                && binding
                                    .result_slots()
                                    .first()
                                    .and_then(|slot| results.get(*slot as usize))
                                    .is_some_and(|result| result.id == authority[1])
                        })
                    })
            })
        }
        VirInstruction::Initialize { value, .. }
        | VirInstruction::Write { value, .. }
        | VirInstruction::Store { value, .. } => authority.contains(value),
        VirInstruction::ResourceInitialize {
            value,
            value_permission,
            ..
        } => authority.contains(value) || authority.contains(value_permission),
        _ => false,
    }
}

fn collect_and_check_parents(
    blocks: &[DraftBlock],
    regions: &RegionSolution,
) -> Result<BTreeMap<VirLoanId, VirLoanId>, LoanEndPlanningError> {
    let mut parents = BTreeMap::new();
    for instruction in blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction {
            DraftInstruction::Canonical(instruction) => Some(&instruction.instruction),
            DraftInstruction::Pending(_) => None,
        })
    {
        let VirInstruction::LoanReborrow { effect, .. } = instruction else {
            continue;
        };
        let parent = effect
            .parent
            .ok_or(LoanEndPlanningError::InvalidParentGraph(effect.loan))?;
        if parents.insert(effect.loan, parent).is_some() || parent >= effect.loan {
            return Err(LoanEndPlanningError::InvalidParentGraph(effect.loan));
        }
        let parent_region = blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .find_map(|candidate| match candidate {
                DraftInstruction::Canonical(candidate) => match &candidate.instruction {
                    VirInstruction::LoanBegin {
                        effect: parent_effect,
                        ..
                    }
                    | VirInstruction::LoanReborrow {
                        effect: parent_effect,
                        ..
                    } if parent_effect.loan == parent => Some(parent_effect.region),
                    _ => None,
                },
                DraftInstruction::Pending(_) => None,
            })
            .ok_or(LoanEndPlanningError::InvalidParentGraph(effect.loan))?;
        if !regions.contains(effect.region, parent_region) {
            return Err(LoanEndPlanningError::MissingRegionInclusion {
                loan: effect.loan,
                parent,
            });
        }
    }
    Ok(parents)
}

fn loan_depth(
    mut loan: VirLoanId,
    parents: &BTreeMap<VirLoanId, VirLoanId>,
) -> Result<usize, LoanEndPlanningError> {
    let original = loan;
    for depth in 0..=MAX_PARENT_DEPTH {
        let Some(parent) = parents.get(&loan).copied() else {
            return Ok(depth);
        };
        if parent >= loan {
            return Err(LoanEndPlanningError::InvalidParentGraph(original));
        }
        loan = parent;
    }
    Err(LoanEndPlanningError::InvalidParentGraph(original))
}

fn remap_source_locations(
    function: VirFunctionId,
    entries: &mut [VirSourceMapEntry],
    remapped: &BTreeMap<(VirBlockId, u64), u64>,
) -> Result<(), LoanEndPlanningError> {
    for entry in entries {
        let location = match entry.location() {
            VirLocation::Instruction {
                function: owner,
                block,
                ordinal,
            } if owner == function => VirLocation::Instruction {
                function: owner,
                block,
                ordinal: remapped
                    .get(&(block, ordinal))
                    .copied()
                    .ok_or(LoanEndPlanningError::MissingSourceLocation { block, ordinal })?,
            },
            VirLocation::CallEdge {
                function: owner,
                block,
                instruction,
            } if owner == function => VirLocation::CallEdge {
                function: owner,
                block,
                instruction: remapped.get(&(block, instruction)).copied().ok_or(
                    LoanEndPlanningError::MissingSourceLocation {
                        block,
                        ordinal: instruction,
                    },
                )?,
            },
            location => location,
        };
        entry.set_location(location);
    }
    Ok(())
}

struct RegionSolution {
    relations: BTreeSet<(crate::VirBorrowRegionId, crate::VirBorrowRegionId)>,
}

impl RegionSolution {
    fn solve(constraints: &[DraftRegionConstraint]) -> Result<Self, LoanEndPlanningError> {
        if constraints.len() > MAX_REGION_RELATIONS {
            return Err(LoanEndPlanningError::RegionRelationBudget);
        }
        let direct = constraints
            .iter()
            .map(|constraint| (constraint.subregion, constraint.superregion))
            .collect::<BTreeSet<_>>();
        let nodes = direct
            .iter()
            .flat_map(|(subregion, superregion)| [*subregion, *superregion])
            .collect::<BTreeSet<_>>();
        let mut relations = BTreeSet::new();
        for start in nodes {
            let mut pending = vec![start];
            let mut visited = BTreeSet::new();
            while let Some(current) = pending.pop() {
                for (_, next) in direct.iter().filter(|(from, _)| *from == current) {
                    if *next == start {
                        return Err(LoanEndPlanningError::CyclicRegionConstraints);
                    }
                    if visited.insert(*next) {
                        if relations.len() >= MAX_REGION_RELATIONS {
                            return Err(LoanEndPlanningError::RegionRelationBudget);
                        }
                        relations.insert((start, *next));
                        pending.push(*next);
                    }
                }
            }
        }
        Ok(Self { relations })
    }

    fn contains(
        &self,
        subregion: crate::VirBorrowRegionId,
        superregion: crate::VirBorrowRegionId,
    ) -> bool {
        subregion == superregion || self.relations.contains(&(subregion, superregion))
    }
}

#[cfg(test)]
mod tests {
    use super::{LoanEndPlanningError, RegionSolution};
    use crate::frontend::lower::draft::DraftRegionConstraint;
    use crate::vir::VirBorrowRegionId;

    #[test]
    fn region_solution_computes_bounded_transitive_inclusion() {
        let constraints = [
            DraftRegionConstraint {
                subregion: VirBorrowRegionId::new(2),
                superregion: VirBorrowRegionId::new(1),
            },
            DraftRegionConstraint {
                subregion: VirBorrowRegionId::new(1),
                superregion: VirBorrowRegionId::new(0),
            },
        ];
        let solution = RegionSolution::solve(&constraints).expect("acyclic inclusion solves");
        assert!(solution.contains(VirBorrowRegionId::new(2), VirBorrowRegionId::new(0)));
    }

    #[test]
    fn region_solution_rejects_cycles() {
        let constraints = [
            DraftRegionConstraint {
                subregion: VirBorrowRegionId::new(0),
                superregion: VirBorrowRegionId::new(1),
            },
            DraftRegionConstraint {
                subregion: VirBorrowRegionId::new(1),
                superregion: VirBorrowRegionId::new(0),
            },
        ];
        assert!(matches!(
            RegionSolution::solve(&constraints),
            Err(LoanEndPlanningError::CyclicRegionConstraints)
        ));
    }
}
