use std::collections::BTreeMap;

use crate::{ResolvedVirUnit, VirSpecTermId, VirSpecTermKind};

use super::arena::{VcArena, VcLimitError, VcLimits, VcTerm, VcTermId};
#[cfg(test)]
mod tests;

/// Function-local normalizer retaining both source-ID and structural sharing.
pub(in crate::verifier) struct VcNormalizer {
    pub(in crate::verifier) exhausted: bool,
    arena: VcArena,
    normalized: BTreeMap<VirSpecTermId, VcTermId>,
    limits: VcLimits,
    normalization_steps: usize,
}

impl VcNormalizer {
    pub(in crate::verifier) fn new(limits: VcLimits) -> Self {
        Self {
            exhausted: false,
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
        let mut cache = std::mem::take(&mut self.normalized);
        let result = self.normalize_with(unit, root, &BTreeMap::new(), &mut cache);
        self.note_limit(&result);
        self.normalized = cache;
        result
    }

    /// Binder IDs, not display names, determine substitution. A witness is
    /// normalized in the outer scope before insertion. Source-ID caching must
    /// never cross substitution environments; only the immutable arena is shared.
    pub(in crate::verifier) fn normalize_bound(
        &mut self,
        unit: &ResolvedVirUnit<'_>,
        root: VirSpecTermId,
        bindings: &BTreeMap<u32, VcTermId>,
    ) -> Result<VcTermId, VcLimitError> {
        if bindings.is_empty() {
            self.normalize(unit, root)
        } else {
            let result = self.normalize_with(unit, root, bindings, &mut BTreeMap::new());
            self.note_limit(&result);
            result
        }
    }

    fn note_limit(&mut self, result: &Result<VcTermId, VcLimitError>) {
        self.exhausted |= matches!(
            result,
            Err(VcLimitError::NodeBudget | VcLimitError::NormalizationBudget)
        );
    }

    fn normalize_with(
        &mut self,
        unit: &ResolvedVirUnit<'_>,
        root: VirSpecTermId,
        bindings: &BTreeMap<u32, VcTermId>,
        cache: &mut BTreeMap<VirSpecTermId, VcTermId>,
    ) -> Result<VcTermId, VcLimitError> {
        if let Some(id) = cache.get(&root) {
            return Ok(*id);
        }

        let terms = unit.as_unit().specs.terms();
        let mut stack = vec![(root, false)];
        while let Some((source_id, expanded)) = stack.pop() {
            if cache.contains_key(&source_id) {
                continue;
            }
            let source = terms
                .get(source_id.get() as usize)
                .filter(|term| term.id == source_id)
                .ok_or(VcLimitError::MalformedValidatedInput)?;

            if expanded {
                if cache.len() >= self.limits.max_nodes {
                    return Err(VcLimitError::NodeBudget);
                }
                let replacement = match source.kind {
                    VirSpecTermKind::Binder(id) => bindings.get(&id.get()).copied(),
                    _ => None,
                };
                let normalized_id = if let Some(id) = replacement {
                    self.arena
                        .get(id)
                        .ok_or(VcLimitError::MalformedValidatedInput)?;
                    id
                } else {
                    self.arena.intern(
                        Self::normalized_term(&source.kind, cache)?,
                        self.limits.max_nodes,
                    )?
                };
                cache.insert(source_id, normalized_id);
                continue;
            }

            self.charge_normalization(1usize.saturating_add(child_count(&source.kind)))?;
            stack.push((source_id, true));
            push_children_reversed(&mut stack, &source.kind, cache);
        }

        cache
            .get(&root)
            .copied()
            .ok_or(VcLimitError::MalformedValidatedInput)
    }

    fn normalized_term(
        kind: &VirSpecTermKind,
        cache: &BTreeMap<VirSpecTermId, VcTermId>,
    ) -> Result<VcTerm, VcLimitError> {
        let child = |id: VirSpecTermId| {
            cache
                .get(&id)
                .copied()
                .ok_or(VcLimitError::MalformedValidatedInput)
        };
        Ok(match kind {
            VirSpecTermKind::CheckedAdd { left, right } => {
                VcTerm::CheckedAdd(child(*left)?, child(*right)?)
            }
            VirSpecTermKind::CheckedSub { left, right } => {
                VcTerm::CheckedSub(child(*left)?, child(*right)?)
            }
            VirSpecTermKind::CheckedScale { operand, stride } => {
                VcTerm::CheckedScale(child(*operand)?, *stride)
            }
            VirSpecTermKind::RangeContains {
                outer_start: a,
                outer_end: b,
                inner_start: c,
                inner_end: d,
            } => VcTerm::RangeContains([child(*a)?, child(*b)?, child(*c)?, child(*d)?]),
            VirSpecTermKind::RangeDisjoint {
                left_start: a,
                left_end: b,
                right_start: c,
                right_end: d,
            } => VcTerm::RangeDisjoint([child(*a)?, child(*b)?, child(*c)?, child(*d)?]),
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
        VirSpecTermKind::CheckedAdd { .. } | VirSpecTermKind::CheckedSub { .. } => 2,
        VirSpecTermKind::CheckedScale { .. } => 1,
        VirSpecTermKind::RangeContains { .. } | VirSpecTermKind::RangeDisjoint { .. } => 4,
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
        VirSpecTermKind::CheckedAdd { left, right }
        | VirSpecTermKind::CheckedSub { left, right } => {
            push(*right);
            push(*left);
        }
        VirSpecTermKind::CheckedScale { operand, .. } => push(*operand),
        VirSpecTermKind::RangeContains {
            outer_start: a,
            outer_end: b,
            inner_start: c,
            inner_end: d,
        }
        | VirSpecTermKind::RangeDisjoint {
            left_start: a,
            left_end: b,
            right_start: c,
            right_end: d,
        } => {
            push(*d);
            push(*c);
            push(*b);
            push(*a);
        }
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
