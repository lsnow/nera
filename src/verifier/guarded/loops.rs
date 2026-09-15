//! Bounded disjunction of whole resource states at cyclic CFG entries.
//! Partition selection never proves an operation: canonical transfer still
//! checks every surviving case. Exhaustion merges ALL cases and is sticky.
use super::*;

impl ConditionalResourceState {
    #[cfg(test)]
    pub(in crate::verifier) fn join_loop(
        &self,
        incoming: &Self,
        limits: GuardedStateLimits,
    ) -> Result<Self, ResourceJoinError> {
        self.merge_loop(incoming, limits, false, &[])
    }

    #[cfg(test)]
    pub(in crate::verifier) fn widen(
        &self,
        incoming: &Self,
        limits: GuardedStateLimits,
    ) -> Result<Self, ResourceJoinError> {
        self.merge_loop(incoming, limits, true, &[])
    }

    pub(in crate::verifier) fn merge_loop(
        &self,
        incoming: &Self,
        limits: GuardedStateLimits,
        widening: bool,
        cuts: &[u64],
    ) -> Result<Self, ResourceJoinError> {
        let mut losses = self.precision_losses.clone();
        losses.extend(incoming.precision_losses.iter().copied());
        let mut cases = Vec::<ResourceCase>::new();
        // First join within each key; widening must compare the previous
        // partition with the complete incoming partition, not depend on how
        // many predecessors happen to deliver the same phase.
        for case in self.cases.iter().chain(&incoming.cases) {
            if let Some(previous) = cases
                .iter_mut()
                .find(|p| p.same_loop_partition(case) && p.same_loop_predicates(case, cuts))
            {
                *previous = previous.join(case)?;
            } else {
                cases.push(case.clone());
            }
        }
        let exhausted = limits.max_cases == 0
            || cases.len() > limits.max_cases
            || losses.contains(&GuardedStatePrecisionLoss::CaseBudget)
            || losses.contains(&GuardedStatePrecisionLoss::LoopPartitionBudget);
        if exhausted {
            losses.insert(GuardedStatePrecisionLoss::LoopPartitionBudget);
            losses.insert(GuardedStatePrecisionLoss::CaseBudget);
            let joined = collapse_cases(&cases)?;
            let state = if widening {
                self.collapsed()?.widen(&joined)?
            } else {
                joined
            };
            if widening {
                losses.insert(GuardedStatePrecisionLoss::LoopWidening);
            }
            return normalize(
                vec![state],
                losses,
                limits,
                GuardedReduction::PreserveGuards,
            );
        }
        if widening {
            for case in &mut cases {
                let previous = self
                    .cases
                    .iter()
                    .filter(|p| p.same_loop_partition(case) && p.same_loop_predicates(case, cuts))
                    .cloned()
                    .collect::<Vec<_>>();
                if !previous.is_empty() {
                    let widened = collapse_cases(&previous)?.widen_loop_predicates(case, cuts)?;
                    if widened != *case {
                        losses.insert(GuardedStatePrecisionLoss::LoopWidening);
                    }
                    *case = widened;
                }
            }
        }
        // Selective reduction is for ordinary joins; it must not undo the
        // chosen loop partition by merging complementary flag guards.
        normalize(cases, losses, limits, GuardedReduction::PreserveGuards)
    }
}

#[cfg(test)]
mod tests;
