//! Structural local liveness for HIR-to-VIR environment edges.
//!
//! This analysis only minimizes runtime block parameters. It does not infer
//! ownership or permission state; the VIR verifier remains authoritative for
//! those facts.

use std::collections::BTreeSet;

use super::invalid_hir;
use crate::frontend::FrontendFailure;
use crate::frontend::hir::{
    HirBlock, HirExpression, HirExpressionKind, HirForSource, HirLocalId, HirLoopId, HirMatchArm,
    HirPlace, HirPlaceBase, HirProjectionKind, HirStatement, HirStatementKind,
};

const MAX_LOOP_LIVENESS_ITERATIONS: usize = 256;

/// Local sets at the two structured targets of one active loop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LoopLiveness {
    pub(super) loop_id: HirLoopId,
    pub(super) header: Vec<HirLocalId>,
    pub(super) exit: Vec<HirLocalId>,
}

pub(super) fn match_arm_live_in(
    arm: &HirMatchArm,
    live_after_match: &[HirLocalId],
    active_loops: &[LoopLiveness],
) -> Result<Vec<HirLocalId>, FrontendFailure> {
    let mut live = block_live_in(&arm.body, live_after_match, active_loops)?
        .into_iter()
        .collect::<BTreeSet<_>>();
    if let Some(guard) = &arm.guard {
        collect_expression(guard, &mut live);
    }
    Ok(live.into_iter().collect())
}

pub(super) fn statement_live_outs(
    block: &HirBlock,
    live_after_block: &[HirLocalId],
    active_loops: &[LoopLiveness],
) -> Result<Vec<Vec<HirLocalId>>, FrontendFailure> {
    let mut live = live_after_block.iter().copied().collect::<BTreeSet<_>>();
    let mut reversed = Vec::with_capacity(block.statements.len());
    for statement in block.statements.iter().rev() {
        reversed.push(live.iter().copied().collect());
        live = statement_live_in(statement, live, active_loops)?;
    }
    reversed.reverse();
    Ok(reversed)
}

pub(super) fn block_live_in(
    block: &HirBlock,
    live_after_block: &[HirLocalId],
    active_loops: &[LoopLiveness],
) -> Result<Vec<HirLocalId>, FrontendFailure> {
    let mut live = live_after_block.iter().copied().collect::<BTreeSet<_>>();
    for statement in block.statements.iter().rev() {
        live = statement_live_in(statement, live, active_loops)?;
    }
    for local in &block.locals {
        live.remove(local);
    }
    Ok(live.into_iter().collect())
}

fn statement_live_in(
    statement: &HirStatement,
    mut live: BTreeSet<HirLocalId>,
    active_loops: &[LoopLiveness],
) -> Result<BTreeSet<HirLocalId>, FrontendFailure> {
    match &statement.kind {
        HirStatementKind::Declare { local } => {
            live.remove(local);
        }
        HirStatementKind::Let { local, value } => {
            live.remove(local);
            collect_expression(value, &mut live);
        }
        HirStatementKind::Assign { destination, value } => {
            collect_place(destination, &mut live);
            collect_expression(value, &mut live);
        }
        HirStatementKind::Free { pointer } => {
            live.insert(*pointer);
        }
        HirStatementKind::Return { value } => {
            live.clear();
            if let Some(value) = value {
                collect_expression(value, &mut live);
            }
        }
        HirStatementKind::Block { block } => {
            live = block_live_in(
                block,
                &live.iter().copied().collect::<Vec<_>>(),
                active_loops,
            )?
            .into_iter()
            .collect();
        }
        HirStatementKind::If {
            condition,
            then_block,
            else_block,
        } => {
            let live_out = live.iter().copied().collect::<Vec<_>>();
            let mut branches = block_live_in(then_block, &live_out, active_loops)?
                .into_iter()
                .collect::<BTreeSet<_>>();
            if let Some(else_block) = else_block {
                branches.extend(block_live_in(else_block, &live_out, active_loops)?);
            } else {
                branches.extend(live);
            }
            collect_expression(condition, &mut branches);
            live = branches;
        }
        HirStatementKind::While {
            loop_id,
            condition,
            body,
        } => {
            live = loop_liveness(
                *loop_id,
                condition,
                body,
                &live.iter().copied().collect::<Vec<_>>(),
                active_loops,
                statement.span,
            )?
            .header
            .into_iter()
            .collect();
        }
        HirStatementKind::For {
            loop_id,
            source,
            body,
            ..
        } => {
            let HirForSource::IntegerRange { start, end, .. } = source;
            live = for_loop_liveness(
                *loop_id,
                body,
                &live.iter().copied().collect::<Vec<_>>(),
                active_loops,
                statement.span,
            )?
            .header
            .into_iter()
            .collect();
            // Bounds execute once in source order before the loop header.
            collect_expression(end, &mut live);
            collect_expression(start, &mut live);
        }
        HirStatementKind::Match { scrutinee, arms } => {
            let live_out = live.iter().copied().collect::<Vec<_>>();
            let mut alternatives = BTreeSet::new();
            for arm in arms {
                let mut arm_live = block_live_in(&arm.body, &live_out, active_loops)?
                    .into_iter()
                    .collect::<BTreeSet<_>>();
                if let Some(guard) = &arm.guard {
                    collect_expression(guard, &mut arm_live);
                }
                alternatives.extend(arm_live);
            }
            collect_expression(scrutinee, &mut alternatives);
            live = alternatives;
        }
        HirStatementKind::Break { target } | HirStatementKind::Continue { target } => {
            let target = active_loops
                .iter()
                .rev()
                .find(|active| active.loop_id == *target)
                .ok_or_else(|| invalid_hir(statement.span))?;
            live = if matches!(&statement.kind, HirStatementKind::Break { .. }) {
                target.exit.iter().copied().collect()
            } else {
                target.header.iter().copied().collect()
            };
        }
        HirStatementKind::Evaluate { expression } => collect_expression(expression, &mut live),
    }
    Ok(live)
}

pub(super) fn for_loop_liveness(
    loop_id: HirLoopId,
    body: &HirBlock,
    live_after_loop: &[HirLocalId],
    active_loops: &[LoopLiveness],
    source_span: crate::ByteSpan,
) -> Result<LoopLiveness, FrontendFailure> {
    let exit = live_after_loop.iter().copied().collect::<BTreeSet<_>>();
    let mut header = exit.clone();

    for _ in 0..MAX_LOOP_LIVENESS_ITERATIONS {
        let candidate = LoopLiveness {
            loop_id,
            header: header.iter().copied().collect(),
            exit: exit.iter().copied().collect(),
        };
        let mut loops = active_loops.to_vec();
        loops.push(candidate.clone());
        let mut next = exit.clone();
        next.extend(block_live_in(body, &candidate.header, &loops)?);
        if next == header {
            return Ok(candidate);
        }
        header = next;
    }
    Err(FrontendFailure::elaboration(
        source_span,
        "for-loop liveness did not converge within the frontend limit",
    ))
}

pub(super) fn loop_liveness(
    loop_id: HirLoopId,
    condition: &HirExpression,
    body: &HirBlock,
    live_after_loop: &[HirLocalId],
    active_loops: &[LoopLiveness],
    source_span: crate::ByteSpan,
) -> Result<LoopLiveness, FrontendFailure> {
    let exit = live_after_loop.iter().copied().collect::<BTreeSet<_>>();
    let mut header = exit.clone();
    collect_expression(condition, &mut header);

    for _ in 0..MAX_LOOP_LIVENESS_ITERATIONS {
        let candidate = LoopLiveness {
            loop_id,
            header: header.iter().copied().collect(),
            exit: exit.iter().copied().collect(),
        };
        let mut loops = active_loops.to_vec();
        loops.push(candidate.clone());
        let mut next = exit.clone();
        collect_expression(condition, &mut next);
        next.extend(block_live_in(body, &candidate.header, &loops)?);
        if next == header {
            return Ok(candidate);
        }
        header = next;
    }
    Err(FrontendFailure::elaboration(
        source_span,
        "loop liveness did not converge within the frontend limit",
    ))
}

fn collect_expression(expression: &HirExpression, live: &mut BTreeSet<HirLocalId>) {
    match &expression.kind {
        HirExpressionKind::Unit
        | HirExpressionKind::Integer(_)
        | HirExpressionKind::Bool(_)
        | HirExpressionKind::Allocate { .. } => {}
        HirExpressionKind::TupleConstructor { elements }
        | HirExpressionKind::ArrayConstructor { elements } => {
            for element in elements {
                collect_expression(element, live);
            }
        }
        HirExpressionKind::ArrayRepeatConstructor { value, .. } => {
            collect_expression(value, live);
        }
        HirExpressionKind::StructConstructor { fields }
        | HirExpressionKind::EnumConstructor { fields, .. } => {
            for field in fields {
                collect_expression(&field.value, live);
            }
        }
        HirExpressionKind::Compare { left, right, .. }
        | HirExpressionKind::PointerDistance {
            begin: left,
            end: right,
        } => {
            collect_expression(left, live);
            collect_expression(right, live);
        }
        HirExpressionKind::WordAdd { operands, .. } => {
            for operand in operands {
                collect_expression(operand, live);
            }
        }
        HirExpressionKind::PointerOffset { base, .. } => collect_expression(base, live),
        HirExpressionKind::Read { place, .. }
        | HirExpressionKind::Length { place }
        | HirExpressionKind::OwnerAddress { place }
        | HirExpressionKind::Borrow { place, .. }
        | HirExpressionKind::RawAddress { place, .. } => collect_place(place, live),
        HirExpressionKind::Call(call) => {
            for argument in &call.arguments {
                collect_expression(argument, live);
            }
        }
    }
}

fn collect_place(place: &HirPlace, live: &mut BTreeSet<HirLocalId>) {
    let HirPlaceBase::Local(base) = place.base;
    live.insert(base);
    for projection in &place.projections {
        match &projection.kind {
            HirProjectionKind::DynamicIndex { index } => collect_expression(index, live),
            HirProjectionKind::Slice { start, end } => {
                for bound in start.iter().chain(end) {
                    collect_expression(bound, live);
                }
            }
            HirProjectionKind::Dereference
            | HirProjectionKind::Field { .. }
            | HirProjectionKind::TupleElement { .. }
            | HirProjectionKind::ConstantIndex { .. }
            | HirProjectionKind::Downcast { .. } => {}
        }
    }
}
