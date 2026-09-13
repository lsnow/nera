use std::collections::BTreeMap;

use crate::VirSpecSnapshot;

/// Stable index into one function-local normalized VC arena.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::verifier) struct VcTermId(u32);

impl VcTermId {
    pub(super) const fn new(raw: u32) -> Self {
        Self(raw)
    }

    pub(super) const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Hash-consed VC node. Children are arena IDs, so source DAG sharing is
/// retained and structurally equal source terms share the same normalized ID.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum VcTerm {
    CheckedAdd(VcTermId, VcTermId),
    CheckedSub(VcTermId, VcTermId),
    CheckedScale(VcTermId, u64),
    RangeContains([VcTermId; 4]),
    RangeDisjoint([VcTermId; 4]),
    Bool(bool),
    U64(u64),
    Binder(u32),
    Snapshot(VirSpecSnapshot),
    Equal(VcTermId, VcTermId),
    LessThan(VcTermId, VcTermId),
    LessOrEqual(VcTermId, VcTermId),
    Not(VcTermId),
    And(Vec<VcTermId>),
    Or(Vec<VcTermId>),
}

impl VcTerm {
    pub(super) const fn child_count(&self) -> usize {
        match self {
            Self::CheckedAdd(..) | Self::CheckedSub(..) => 2,
            Self::CheckedScale(..) => 1,
            Self::RangeContains(..) | Self::RangeDisjoint(..) => 4,
            Self::Equal(..) | Self::LessThan(..) | Self::LessOrEqual(..) => 2,
            Self::Not(_) => 1,
            Self::And(operands) | Self::Or(operands) => operands.len(),
            Self::Bool(_) | Self::U64(_) | Self::Binder(_) | Self::Snapshot(_) => 0,
        }
    }

    pub(super) fn child_at(&self, index: usize) -> Option<VcTermId> {
        match self {
            Self::CheckedAdd(left, right) | Self::CheckedSub(left, right) => {
                [*left, *right].get(index).copied()
            }
            Self::CheckedScale(operand, _) => (index == 0).then_some(*operand),
            Self::RangeContains(ends) | Self::RangeDisjoint(ends) => ends.get(index).copied(),
            Self::Equal(left, right)
            | Self::LessThan(left, right)
            | Self::LessOrEqual(left, right) => [*left, *right].get(index).copied(),
            Self::Not(operand) => (index == 0).then_some(*operand),
            Self::And(operands) | Self::Or(operands) => operands.get(index).copied(),
            Self::Bool(_) | Self::U64(_) | Self::Binder(_) | Self::Snapshot(_) => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::verifier) struct VcLimits {
    pub(in crate::verifier) max_nodes: usize,
    pub(in crate::verifier) max_normalization_steps: usize,
    pub(in crate::verifier) max_queries: usize,
    pub(in crate::verifier) max_query_steps: usize,
}

impl Default for VcLimits {
    fn default() -> Self {
        Self {
            max_nodes: 65_536,
            max_normalization_steps: 262_144,
            max_queries: 4_096,
            max_query_steps: 262_144,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::verifier) enum VcLimitError {
    NodeBudget,
    NormalizationBudget,
    MalformedValidatedInput,
}

#[derive(Default)]
pub(in crate::verifier) struct VcArena {
    nodes: Vec<VcTerm>,
    interned: BTreeMap<VcTerm, VcTermId>,
}

impl VcArena {
    pub(super) fn get(&self, id: VcTermId) -> Option<&VcTerm> {
        self.nodes.get(id.index())
    }

    pub(super) fn intern(
        &mut self,
        term: VcTerm,
        max_nodes: usize,
    ) -> Result<VcTermId, VcLimitError> {
        if let Some(id) = self.interned.get(&term) {
            return Ok(*id);
        }
        if self.nodes.len() >= max_nodes {
            return Err(VcLimitError::NodeBudget);
        }
        let raw = u32::try_from(self.nodes.len()).map_err(|_| VcLimitError::NodeBudget)?;
        let id = VcTermId::new(raw);
        self.nodes.push(term.clone());
        self.interned.insert(term, id);
        Ok(id)
    }
}

#[cfg(test)]
mod tests {
    use super::{VcArena, VcLimitError, VcTerm};

    #[test]
    fn arena_preserves_structural_sharing_and_enforces_the_node_budget() {
        let mut arena = VcArena::default();
        let first = arena
            .intern(VcTerm::Bool(true), 2)
            .expect("first node fits");
        let shared = arena
            .intern(VcTerm::Bool(true), 2)
            .expect("interned node does not spend the budget twice");
        assert_eq!(first, shared);

        arena
            .intern(VcTerm::Not(first), 2)
            .expect("second distinct node fits");
        assert_eq!(
            arena.intern(VcTerm::Bool(false), 2),
            Err(VcLimitError::NodeBudget)
        );
    }
}
