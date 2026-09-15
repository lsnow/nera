//! A bounded post-fixpoint check, separate from worklist convergence. No state
//! is updated here: every replay starts from the frozen candidate. This reuses
//! the canonical transfer, and is not an independent proof of its correctness.
use super::*;

struct Budget {
    remaining: u64,
    limit: u64,
}
impl Budget {
    fn charge(&mut self, work: u64) -> Result<(), CfgAnalysisError> {
        self.remaining = self
            .remaining
            .checked_sub(work)
            .ok_or(CfgAnalysisError::ClosureAuditBudgetExceeded { limit: self.limit })?;
        Ok(())
    }
}

fn failure(block: VirBlockId, reason: &'static str) -> CfgAnalysisError {
    CfgAnalysisError::ClosureAuditFailed { block, reason }
}

/// Every incoming whole case must be included; choosing only the favorable
/// source case would allow a dead permission to disappear at a merge.
fn covered(
    target: &ConditionalResourceState,
    incoming: &ConditionalResourceState,
    block: VirBlockId,
    budget: &mut Budget,
) -> Result<(), CfgAnalysisError> {
    for case in incoming.cases() {
        let mut found = false;
        for candidate in target.cases() {
            budget.charge(1)?;
            if candidate.covers_cfg_case(case) {
                found = true;
                break;
            }
        }
        if !found {
            return Err(failure(block, "incoming resource case is not covered"));
        }
    }
    Ok(())
}

pub(super) fn audit(
    context: BlockEvaluationContext<'_, '_>,
    selected: &BTreeSet<crate::VirSpecLoopInvariantId>,
    seed: &ConditionalResourceState,
    frozen: &BTreeMap<VirBlockId, CfgBlockAnalysis>,
    refined: &BTreeSet<VirBlockId>,
    obligations: &BTreeMap<VirBlockId, Vec<CfgObligation>>,
    returns: &BTreeMap<VirBlockId, Vec<FunctionReturnState>>,
) -> Result<(), CfgAnalysisError> {
    let mut budget = Budget {
        remaining: context.config.max_closure_audit_steps,
        limit: context.config.max_closure_audit_steps,
    };
    budget.charge(1)?;
    budget.charge(frozen.len() as u64 + obligations.len() as u64 + returns.len() as u64)?;
    if !frozen.keys().eq(context.blocks.keys())
        || obligations
            .keys()
            .chain(returns.keys())
            .any(|id| !frozen.contains_key(id))
    {
        return Err(failure(
            context.function.entry,
            "frozen CFG block set does not match the function",
        ));
    }
    covered(
        &frozen[&context.function.entry].entry_conditional_state,
        seed,
        context.function.entry,
        &mut budget,
    )?;
    // Replay must not mutate the inference journal or publish additional call
    // evidence. Summary effects still use the same checked registry and limits.
    let journal = std::cell::RefCell::new(super::super::summary::EffectJournal::default());
    let inference_journal = context.summary_context.journal;
    let context = BlockEvaluationContext {
        summary_context: super::super::summary::SummaryTransferContext {
            journal: &journal,
            ..context.summary_context
        },
        ..context
    };
    let mut replay = BTreeMap::new();
    for (&id, block) in context.blocks {
        budget.charge(1)?;
        let entry = &frozen[&id].entry_conditional_state;
        if !entry.is_reachable() {
            if obligations.get(&id).is_some_and(|v| !v.is_empty())
                || returns.get(&id).is_some_and(|v| !v.is_empty())
                || frozen[&id].exit_conditional_state.is_reachable()
                || frozen[&id]
                    .instruction_conditional_states
                    .iter()
                    .any(|s| s.is_reachable())
            {
                return Err(failure(id, "unreachable block retains reachable results"));
            }
            continue;
        }
        budget.charge(
            // Calls may split cases after entry; reserve the per-point case cap,
            // not just the initial case count. Canonical transfer enforces it.
            (block.instructions.len() as u64 + 1).saturating_mul(
                (context.config.max_guarded_cases_per_block as u64)
                    .max(entry.cases().len() as u64)
                    .max(1),
            ),
        )?;
        let evaluated = evaluate_conditional_block(
            &context,
            block,
            entry,
            context.config.guarded_limits(),
            if refined.contains(&id) {
                GuardedReduction::PreserveGuards
            } else {
                GuardedReduction::Selective
            },
        )?;
        replay.insert(id, evaluated);
    }
    let mut induction = loops::Induction::new(
        context.program,
        context.function,
        context.config,
        selected,
        context.summary_context.registry,
    )?;
    // Establish fresh resource frames before checking any backedge; block ID
    // ordering is not a dominance ordering.
    for preheader in induction.preheaders() {
        if let Some(raw) = replay.get(&preheader) {
            budget.charge(
                (raw.successors.len() as u64 + 1)
                    .saturating_mul(context.config.max_guarded_cases_per_block as u64 + 1),
            )?;
            induction.prime(preheader, context.blocks[&preheader], raw)?;
        }
    }
    for (id, mut evaluated) in replay {
        budget.charge(
            (evaluated.successors.len() as u64 + 1)
                .saturating_mul(context.config.max_guarded_cases_per_block as u64 + 1),
        )?;
        induction.cut_edges(context.blocks[&id], &mut evaluated)?;
        let stored = &frozen[&id];
        if evaluated.instruction_states != stored.instruction_conditional_states
            || evaluated.exit_state != stored.exit_conditional_state
            || evaluated.obligations.as_slice()
                != obligations.get(&id).map_or(&[][..], Vec::as_slice)
            || evaluated.returns.as_slice() != returns.get(&id).map_or(&[][..], Vec::as_slice)
            || evaluated
                .obligations
                .iter()
                .any(|r| !r.obligation().is_proven())
        {
            return Err(failure(
                id,
                "final transfer, obligation or return disagrees with replay",
            ));
        }
        // Includes ordinary backedges, break/continue and loop exit edges. Cut
        // invariant backedges above are checked by their actual proof obligations.
        for successor in evaluated.successors {
            covered(
                &frozen[&successor.block].entry_conditional_state,
                &successor.state,
                successor.block,
                &mut budget,
            )?;
        }
    }
    let replay_journal = journal.borrow();
    let original = inference_journal.borrow();
    if replay_journal.audit_overflow {
        return Err(CfgAnalysisError::RelationEvidenceBudgetExceeded {
            block: context.function.entry,
            limit: context.config.max_summary_evidence,
        });
    }
    // Historical inference events may be broader, but every final effect and
    // call must have been recorded. Comparisons count against the audit budget.
    for event in &replay_journal.events {
        let mut found = false;
        for old in &original.events {
            budget.charge(1)?;
            if old == event {
                found = true;
                break;
            }
        }
        if !found {
            return Err(failure(context.function.entry, "missing final effect"));
        }
    }
    for call in &replay_journal.calls {
        let mut found = false;
        for old in &original.calls {
            budget.charge(1)?;
            if old == call {
                found = true;
                break;
            }
        }
        if !found {
            return Err(failure(
                context.function.entry,
                "missing final call evidence",
            ));
        }
    }
    if replay_journal.incomplete && !original.incomplete {
        return Err(failure(
            context.function.entry,
            "incomplete final effect journal",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
