//! Adapt explicit conjunctive entry facts to scalar state. Numeric solving stays
//! in the relation component; no memory observation or authority is introduced.
use super::*;
use crate::verifier::relation::{
    RelationComparison,
    difference::{DifferenceLimits, DifferencePremise, word},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct EntryComparison {
    left_slot: u32,
    right_slot: u32,
    comparison: RelationComparison,
}

impl PureContract {
    pub(in crate::verifier) fn install_scalar_relations(
        &self,
        state: &mut ResourceState,
        parameters: &[(VirValueId, VirType)],
        limits: DifferenceLimits,
    ) -> Option<()> {
        if self.entry || self.entry_comparisons.is_empty() {
            return Some(());
        }
        let mut premises = Vec::new();
        for comparison in &self.entry_comparisons {
            let &(left, VirType::U64) = parameters.get(comparison.left_slot as usize)? else {
                return None;
            };
            let &(right, VirType::U64) = parameters.get(comparison.right_slot as usize)? else {
                return None;
            };
            premises.push(DifferencePremise::Compare {
                comparison: comparison.comparison,
                left: word(left),
                right: word(right),
            });
        }
        state.learn_relations(&premises, limits);
        Some(())
    }
}

pub(super) fn import_entry_facts(
    unit: &ResolvedVirUnit<'_>,
    root: VirSpecTermId,
    bounds: &mut BTreeMap<S, AbstractValue>,
    comparisons: &mut Vec<EntryComparison>,
) -> Option<()> {
    let term = |id: VirSpecTermId| {
        unit.as_unit()
            .specs
            .terms()
            .get(id.get() as usize)
            .map(|t| &t.kind)
    };
    let parameter = |id| match term(id)? {
        T::Snapshot(
            snapshot @ (S::Parameter { .. }
            | S::Memory {
                parameter: Some(_),
                old: false,
                ..
            }),
        ) => Some(*snapshot),
        _ => None,
    };
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        if seen.len() > VcLimits::default().max_nodes {
            return None;
        }
        let (slot, value) = match term(id)? {
            T::Bool(true) => continue,
            T::And(children) => {
                pending.extend(children);
                continue;
            }
            T::Snapshot(
                snapshot @ (S::Parameter { .. }
                | S::Memory {
                    parameter: Some(_),
                    old: false,
                    ..
                }),
            ) => (*snapshot, AbstractValue::Bool(AbstractBool::True)),
            T::Not(child) => (parameter(*child)?, AbstractValue::Bool(AbstractBool::False)),
            kind @ (T::Equal { left, right }
            | T::LessThan { left, right }
            | T::LessOrEqual { left, right }) => {
                if let (Some(S::Parameter { slot: a, .. }), Some(S::Parameter { slot: b, .. })) =
                    (parameter(*left), parameter(*right))
                {
                    if unit.as_unit().specs.terms().get(left.get() as usize)?.ty
                        != crate::VirSpecType::U64
                        || unit.as_unit().specs.terms().get(right.get() as usize)?.ty
                            != crate::VirSpecType::U64
                    {
                        return None;
                    }
                    let comparison = match kind {
                        T::Equal { .. } => RelationComparison::Equal,
                        T::LessThan { .. } => RelationComparison::LessThan,
                        T::LessOrEqual { .. } => RelationComparison::LessOrEqual,
                        _ => return None,
                    };
                    comparisons.push(EntryComparison {
                        left_slot: a,
                        right_slot: b,
                        comparison,
                    });
                    continue;
                }
                let (slot, literal, reversed) = if let Some(slot) = parameter(*left) {
                    (slot, term(*right)?, false)
                } else {
                    (parameter(*right)?, term(*left)?, true)
                };
                let value = match literal {
                    T::U64(n) => {
                        let (low, high) = match (kind, reversed) {
                            (T::Equal { .. }, _) => (*n, *n),
                            (T::LessThan { .. }, false) => (0, n.checked_sub(1)?),
                            (T::LessThan { .. }, true) => (n.checked_add(1)?, u64::MAX),
                            (T::LessOrEqual { .. }, false) => (0, *n),
                            (T::LessOrEqual { .. }, true) => (*n, u64::MAX),
                            _ => return None,
                        };
                        AbstractValue::U64(U64Interval::new(low, high).ok()?)
                    }
                    T::Bool(b) if matches!(kind, T::Equal { .. }) => AbstractValue::Bool(if *b {
                        AbstractBool::True
                    } else {
                        AbstractBool::False
                    }),
                    _ => return None,
                };
                (slot, value)
            }
            _ => return None,
        };
        let value = if let Some(previous) = bounds.get(&slot) {
            intersect(*previous, value)?
        } else {
            value
        };
        bounds.insert(slot, value);
    }
    Some(())
}
