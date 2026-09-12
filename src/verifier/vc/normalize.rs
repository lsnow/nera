use std::collections::BTreeMap;

use crate::{ResolvedVirUnit, VirSpecTermId, VirSpecTermKind};

use super::arena::{VcArena, VcLimitError, VcLimits, VcTerm, VcTermId};

/// Function-local normalizer retaining both source-ID and structural sharing.
pub(in crate::verifier) struct VcNormalizer {
    arena: VcArena,
    normalized: BTreeMap<VirSpecTermId, VcTermId>,
    limits: VcLimits,
    normalization_steps: usize,
}

impl VcNormalizer {
    pub(in crate::verifier) fn new(limits: VcLimits) -> Self {
        Self {
            arena: VcArena::default(),
            normalized: BTreeMap::new(),
            limits,
            normalization_steps: 0,
        }
    }

    pub(in crate::verifier) const fn arena(&self) -> &VcArena {
        &self.arena
    }

    /// Normalizes one root without host recursion. Validated VIR terms point
    /// only to earlier same-clause terms; the explicit stack still treats a
    /// missing child as a closed failure rather than relying on that invariant.
    pub(in crate::verifier) fn normalize(
        &mut self,
        unit: &ResolvedVirUnit<'_>,
        root: VirSpecTermId,
    ) -> Result<VcTermId, VcLimitError> {
        if let Some(id) = self.normalized.get(&root) {
            return Ok(*id);
        }

        let terms = unit.as_unit().specs.terms();
        let mut stack = vec![(root, false)];
        while let Some((source_id, expanded)) = stack.pop() {
            if self.normalized.contains_key(&source_id) {
                continue;
            }
            let source = terms
                .get(source_id.get() as usize)
                .filter(|term| term.id == source_id)
                .ok_or(VcLimitError::MalformedValidatedInput)?;

            if expanded {
                let normalized = self.normalized_term(&source.kind)?;
                if self.normalized.len() >= self.limits.max_nodes {
                    return Err(VcLimitError::NodeBudget);
                }
                let normalized_id = self.arena.intern(normalized, self.limits.max_nodes)?;
                self.normalized.insert(source_id, normalized_id);
                continue;
            }

            self.charge_normalization(1usize.saturating_add(child_count(&source.kind)))?;
            stack.push((source_id, true));
            push_children_reversed(&mut stack, &source.kind, &self.normalized);
        }

        self.normalized
            .get(&root)
            .copied()
            .ok_or(VcLimitError::MalformedValidatedInput)
    }

    fn normalized_term(&self, kind: &VirSpecTermKind) -> Result<VcTerm, VcLimitError> {
        let child = |id: VirSpecTermId| {
            self.normalized
                .get(&id)
                .copied()
                .ok_or(VcLimitError::MalformedValidatedInput)
        };
        Ok(match kind {
            VirSpecTermKind::Bool(value) => VcTerm::Bool(*value),
            VirSpecTermKind::U64(value) => VcTerm::U64(*value),
            VirSpecTermKind::Binder(id) => VcTerm::Binder(id.get()),
            VirSpecTermKind::Snapshot(snapshot) => VcTerm::Snapshot(*snapshot),
            VirSpecTermKind::Equal { left, right } => VcTerm::Equal(child(*left)?, child(*right)?),
            VirSpecTermKind::LessThan { left, right } => {
                VcTerm::LessThan(child(*left)?, child(*right)?)
            }
            VirSpecTermKind::LessOrEqual { left, right } => {
                VcTerm::LessOrEqual(child(*left)?, child(*right)?)
            }
            VirSpecTermKind::Not(operand) => VcTerm::Not(child(*operand)?),
            VirSpecTermKind::And(operands) => VcTerm::And(
                operands
                    .iter()
                    .map(|operand| child(*operand))
                    .collect::<Result<_, _>>()?,
            ),
            VirSpecTermKind::Or(operands) => VcTerm::Or(
                operands
                    .iter()
                    .map(|operand| child(*operand))
                    .collect::<Result<_, _>>()?,
            ),
        })
    }

    fn charge_normalization(&mut self, amount: usize) -> Result<(), VcLimitError> {
        self.normalization_steps = self
            .normalization_steps
            .checked_add(amount)
            .ok_or(VcLimitError::NormalizationBudget)?;
        if self.normalization_steps > self.limits.max_normalization_steps {
            return Err(VcLimitError::NormalizationBudget);
        }
        Ok(())
    }
}

const fn child_count(kind: &VirSpecTermKind) -> usize {
    match kind {
        VirSpecTermKind::Equal { .. }
        | VirSpecTermKind::LessThan { .. }
        | VirSpecTermKind::LessOrEqual { .. } => 2,
        VirSpecTermKind::Not(_) => 1,
        VirSpecTermKind::And(operands) | VirSpecTermKind::Or(operands) => operands.len(),
        VirSpecTermKind::Bool(_)
        | VirSpecTermKind::U64(_)
        | VirSpecTermKind::Binder(_)
        | VirSpecTermKind::Snapshot(_) => 0,
    }
}

fn push_children_reversed(
    stack: &mut Vec<(VirSpecTermId, bool)>,
    kind: &VirSpecTermKind,
    normalized: &BTreeMap<VirSpecTermId, VcTermId>,
) {
    let mut push = |id| {
        if !normalized.contains_key(&id) {
            stack.push((id, false));
        }
    };
    match kind {
        VirSpecTermKind::Equal { left, right }
        | VirSpecTermKind::LessThan { left, right }
        | VirSpecTermKind::LessOrEqual { left, right } => {
            push(*right);
            push(*left);
        }
        VirSpecTermKind::Not(operand) => push(*operand),
        VirSpecTermKind::And(operands) | VirSpecTermKind::Or(operands) => {
            for operand in operands.iter().rev() {
                push(*operand);
            }
        }
        VirSpecTermKind::Bool(_)
        | VirSpecTermKind::U64(_)
        | VirSpecTermKind::Binder(_)
        | VirSpecTermKind::Snapshot(_) => {}
    }
}
