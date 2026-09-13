//! Per-Prove resource-use ledger. Entries represent occurrences, not DAG nodes
//! or runtime permission consumption. A failed match drops the entire ledger.
use crate::AccessPermission;
#[cfg(test)]
mod tests;
use crate::verifier::{
    resource::ResourceState,
    transfer::{ObligationStatus, SpecFootprint},
    vc::VcQueryBudget,
};

pub(super) struct MatchLedger {
    used: Vec<SpecFootprint>,
    pairs_left: usize,
}

impl MatchLedger {
    pub(super) fn new(pair_limit: usize) -> Self {
        Self {
            used: Vec::new(),
            pairs_left: pair_limit,
        }
    }

    /// Every entry has already passed the ordinary access/loan checks in this
    /// SAME state. Requested Read is duplicable; an overlapping Write is not.
    /// Different handles/nodes/types never stand in for physical disjointness.
    pub(super) fn reserve(
        &mut self,
        state: &ResourceState,
        next: SpecFootprint,
        budget: &mut VcQueryBudget,
    ) -> Option<ObligationStatus> {
        for previous in &self.used {
            self.pairs_left = self.pairs_left.checked_sub(1).or_else(|| {
                budget.exhausted = true;
                None
            })?;
            budget.charge(1)?;
            if previous.access == AccessPermission::Read && next.access == AccessPermission::Read {
                continue;
            }
            budget.begin_query()?;
            let status = budget.relations.disjoint(
                state,
                previous.provenance,
                previous.range,
                next.provenance,
                next.range,
                budget.relation_limits,
            );
            if status != ObligationStatus::Proven {
                return Some(status);
            }
        }
        self.used.push(next);
        Some(ObligationStatus::Proven)
    }
}
