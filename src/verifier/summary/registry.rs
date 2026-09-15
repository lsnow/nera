//! Private publication boundary. Mutable diagnostic DTOs never enter call transfer.
use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub(crate) struct SummaryRegistry {
    binding: SummaryBinding,
    // SCC trials share sealed interfaces instead of cloning every earlier
    // function's evidence/resources on each iteration.
    entries: BTreeMap<String, std::sync::Arc<FunctionSummary>>,
    assumptions: BTreeSet<String>,
}
impl SummaryRegistry {
    pub fn new(binding: SummaryBinding) -> Self {
        Self {
            binding,
            entries: BTreeMap::new(),
            assumptions: BTreeSet::new(),
        }
    }
    pub fn get(&self, target: &crate::VirCallTarget) -> Option<&FunctionSummary> {
        self.entries
            .get(&target.symbol)
            .filter(|s| {
                s.parameters == target.signature.parameters && s.results == target.signature.results
            })
            .map(|s| s.as_ref())
    }
    pub fn is_inductive(&self, name: &str) -> bool {
        self.assumptions.contains(name)
    }

    /// An actual closed effect summary, never a user frame declaration or an
    /// SCC hypothesis. Call transfer still checks preconditions and records its
    /// normal dependency/audit evidence even when loop content havoc is skipped.
    pub fn preserves_loop_contents(&self, target: &crate::VirCallTarget) -> bool {
        !self.is_inductive(&target.symbol)
            && self.get(target).is_some_and(|s| {
                s.closed
                    && s.audit_complete
                    && s.state == SummaryState::Closed
                    && matches!(&s.effects.may_write, Knowledge::Known(writes) if writes.is_empty())
                    && matches!(&s.effects.may_free, Knowledge::Known(frees) if frees.is_empty())
            })
    }

    /// Scoped trial registry. This clone is discarded, never promoted in place.
    pub fn trial(&self, candidates: &BTreeMap<String, FunctionSummary>) -> Self {
        let mut trial = self.clone();
        trial.assumptions = candidates.keys().cloned().collect();
        trial.entries.extend(
            candidates
                .iter()
                .map(|(name, s)| (name.clone(), std::sync::Arc::new(s.clone()))),
        );
        trial
    }

    /// Atomic publication boundary: complete membership, final replay, external
    /// dependencies, safety and post-fixed-point coverage are all required.
    pub fn publish_component(
        &mut self,
        summaries: &mut BTreeMap<String, FunctionSummary>,
        candidates: &BTreeMap<String, FunctionSummary>,
    ) -> bool {
        let mut members = summaries
            .values()
            .map(|s| s.binding.function)
            .collect::<Vec<_>>();
        members.sort();
        if !self.assumptions.is_empty()
            || summaries.is_empty()
            || summaries.keys().ne(candidates.keys())
            || summaries.iter().any(|(name, s)| {
                !self.ready(s)
                    || !s.recursion.as_ref().is_some_and(|r| {
                        r.outcome == SccOutcome::Closed
                            && r.final_recheck
                            && r.members == members
                            && r.final_candidates
                                .iter()
                                .map(|c| c.function)
                                .eq(members.iter().copied())
                            && r.final_candidates.iter().all(|c| {
                                candidates.values().any(|s| {
                                    s.binding.function == c.function
                                        && s.normal_returns == c.normal_returns
                                })
                            })
                            && r.iterations > 0
                            && r.iterations <= self.binding.config.summary_limits.max_iterations
                            && r.body_analyses >= members.len().saturating_mul(2)
                            && r.body_analyses
                                <= self.binding.config.summary_limits.max_body_analyses
                    })
                    || !recursive::covers(&candidates[name], s)
                    || s.call_uses.iter().any(|c| match c.outcome {
                        CallSummaryOutcome::Inductive => !candidates.contains_key(&c.symbol),
                        CallSummaryOutcome::Applied => !self.entries.contains_key(&c.symbol),
                        _ => true,
                    })
            })
        {
            return false;
        }
        let closed = self
            .entries
            .values()
            .map(|s| s.as_ref())
            .chain(summaries.values())
            .map(|s| s.binding.clone())
            .collect::<Vec<_>>();
        for summary in summaries.values_mut() {
            summary.closed = true;
            summary.state = SummaryState::Closed;
            summary.projected_state = SummaryState::Closed;
            for dependency in &mut summary.dependencies {
                if closed.contains(&dependency.binding) {
                    dependency.state = SummaryState::Closed;
                }
            }
            summary.dependency_states = summary
                .dependencies
                .iter()
                .map(|d| d.state.clone())
                .collect();
        }
        self.entries.extend(
            summaries
                .iter()
                .map(|(name, s)| (name.clone(), std::sync::Arc::new(s.clone()))),
        );
        true
    }
    pub fn close(&mut self, name: &str, summary: &mut FunctionSummary) {
        for dependency in &mut summary.dependencies {
            if self
                .entries
                .values()
                .any(|s| s.binding == dependency.binding)
            {
                dependency.state = SummaryState::Closed;
            }
        }
        summary.dependency_states = summary
            .dependencies
            .iter()
            .map(|d| d.state.clone())
            .collect();
        if !self.ready(summary) {
            return;
        }
        // Publication requires all body-call dependencies to have been applied.
        if summary
            .call_uses
            .iter()
            .any(|c| c.outcome != CallSummaryOutcome::Applied)
        {
            return;
        }
        summary.closed = true;
        summary.state = SummaryState::Closed;
        summary.projected_state = SummaryState::Closed;
        self.entries
            .insert(name.into(), std::sync::Arc::new(summary.clone()));
    }
    fn ready(&self, summary: &FunctionSummary) -> bool {
        summary.audit_complete
            && summary.binding.unit == self.binding.unit
            && summary.binding.config == self.binding.config
            && summary.state == SummaryState::Candidate
            && summary
                .faults
                .requirements
                .iter()
                .all(|r| r.status.is_proven())
            && matches!(&summary.normal_returns, Knowledge::Known(alternatives)
                if alternatives.iter().any(|a| !a.worlds.is_empty())
                    && alternatives.iter().flat_map(|a| &a.worlds).all(|w|
                        w.effects.may_read != Knowledge::Unknown && w.effects.may_write != Knowledge::Unknown && w.effects.may_free != Knowledge::Unknown))
    }
}

/// Iterative Kosaraju plus a callee-first condensation worklist. Neither the
/// graph walk nor SCC processing uses the host call stack for source recursion.
#[derive(Debug)]
pub(crate) struct Component {
    pub members: Vec<VirFunctionId>,
    pub recursive: bool,
}
pub(crate) fn components(program: &ResolvedVirUnit<'_>) -> Vec<Component> {
    let graph: BTreeMap<_, BTreeSet<_>> = program
        .runtime()
        .functions
        .iter()
        .map(|f| {
            let edges = f
                .blocks
                .iter()
                .flat_map(|b| &b.instructions)
                .filter_map(|i| {
                    if let crate::VirInstruction::Call { target, .. } = &i.instruction {
                        program.runtime().call_target_id(target)
                    } else {
                        None
                    }
                })
                .collect();
            (f.id, edges)
        })
        .collect();
    let mut reverse: BTreeMap<_, BTreeSet<_>> =
        graph.keys().map(|id| (*id, BTreeSet::new())).collect();
    for (&id, edges) in &graph {
        for edge in edges {
            reverse.get_mut(edge).unwrap().insert(id);
        }
    }
    let mut visited = BTreeSet::new();
    let mut finish = Vec::new();
    for &root in graph.keys() {
        let mut stack = vec![(root, false)];
        while let Some((id, expanded)) = stack.pop() {
            if expanded {
                finish.push(id);
                continue;
            }
            if !visited.insert(id) {
                continue;
            }
            stack.push((id, true));
            stack.extend(graph[&id].iter().rev().map(|id| (*id, false)));
        }
    }
    visited.clear();
    let mut groups = BTreeMap::new();
    let mut owners = BTreeMap::new();
    for root in finish.into_iter().rev() {
        if visited.contains(&root) {
            continue;
        }
        let mut members = Vec::new();
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            members.push(id);
            stack.extend(reverse[&id].iter().rev().copied());
        }
        members.sort();
        let key = members[0];
        for id in &members {
            owners.insert(*id, key);
        }
        groups.insert(
            key,
            Component {
                recursive: members.len() > 1 || graph[&key].contains(&key),
                members,
            },
        );
    }
    let mut deps: BTreeMap<_, BTreeSet<_>> = groups
        .iter()
        .map(|(&key, c)| {
            (
                key,
                c.members
                    .iter()
                    .flat_map(|id| &graph[id])
                    .map(|id| owners[id])
                    .filter(|id| *id != key)
                    .collect(),
            )
        })
        .collect();
    let mut ordered = Vec::new();
    while let Some(key) = deps
        .iter()
        .find_map(|(&key, deps)| deps.is_empty().then_some(key))
    {
        deps.remove(&key);
        ordered.push(groups.remove(&key).unwrap());
        for set in deps.values_mut() {
            set.remove(&key);
        }
    }
    debug_assert!(groups.is_empty(), "the SCC condensation is acyclic");
    ordered
}
