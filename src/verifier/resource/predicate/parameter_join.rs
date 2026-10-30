//! CFG evidence for public logical parameters. Alias records are produced by
//! actual edge projection and invalidated by writes; scalar bounds are never
//! evidence that two captures denote the same runtime value.
use super::*;
use crate::predicate_logic::{InstanceScope, LogicBudget};

pub(super) struct JoinedParameters {
    pub values: Vec<logic::PredicateLogicValue>,
    pub aliases: BTreeMap<VirValueId, logic::LocalSnapshot>,
}

impl ResourceState {
    pub(super) fn join_predicate_parameters(
        &self,
        other: &Self,
        left: &PredicateInstance,
        right: &PredicateInstance,
        target: InstanceScope,
        budget: &mut LogicBudget,
    ) -> Result<JoinedParameters, PredicateError> {
        self.merge_predicate_parameters(other, left, right, target, budget, false)
    }

    pub(super) fn widen_predicate_parameters(
        &self,
        other: &Self,
        left: &PredicateInstance,
        right: &PredicateInstance,
        target: InstanceScope,
        budget: &mut LogicBudget,
    ) -> Result<JoinedParameters, PredicateError> {
        self.merge_predicate_parameters(other, left, right, target, budget, true)
    }

    fn merge_predicate_parameters(
        &self,
        other: &Self,
        left: &PredicateInstance,
        right: &PredicateInstance,
        target: InstanceScope,
        budget: &mut LogicBudget,
        widen: bool,
    ) -> Result<JoinedParameters, PredicateError> {
        if left.logical_local_aliases.len() > MAX_PREDICATE_LOCAL_ALIASES
            || right.logical_local_aliases.len() > MAX_PREDICATE_LOCAL_ALIASES
        {
            return Err(PredicateError::Budget);
        }
        let mut left_alignment = logic::ParameterAlignment::new(self, left, budget)?;
        let mut right_alignment = logic::ParameterAlignment::new(other, right, budget)?;
        let mut pairs = BTreeMap::<_, Vec<_>>::new();
        let mut left_partners = BTreeMap::<_, BTreeSet<_>>::new();
        let mut right_partners = BTreeMap::<_, BTreeSet<_>>::new();
        // Include private fanout as well: one predecessor's single capture
        // must not identify two distinct captures on the other predecessor.
        for id in self.values.keys() {
            budget.charge(1).map_err(|_| PredicateError::Budget)?;
            let (Some(a), Some(b)) = (
                self.predicate_slot_capture(left, *id),
                other.predicate_slot_capture(right, *id),
            ) else {
                continue;
            };
            if a.1 != b.1 {
                continue;
            }
            pairs.entry((a, b)).or_default().push(*id);
            left_partners.entry(a).or_default().insert(b);
            right_partners.entry(b).or_default().insert(a);
        }
        let mut aliases = BTreeMap::new();
        for ((a, b), ids) in pairs {
            budget
                .charge(ids.len())
                .map_err(|_| PredicateError::Budget)?;
            if left_partners[&a].len() != 1
                || right_partners[&b].len() != 1
                || !left_alignment.contains(&a)
                || !right_alignment.contains(&b)
            {
                continue;
            }
            // A common unchanged historical origin survives the runtime join;
            // retain it instead of inventing a redundant Local representation.
            if a == b && !matches!(a.0, logic::ScalarCapture::Local(_)) {
                continue;
            }
            let value = ids[0];
            left_alignment.bind(a, value, budget)?;
            right_alignment.bind(b, value, budget)?;
            for id in ids {
                aliases.insert(
                    id,
                    logic::LocalSnapshot {
                        scope: target,
                        value,
                    },
                );
            }
        }
        let values = left_alignment.normalize(target, budget)?;
        let other_values = right_alignment.normalize(target, budget)?;
        if values.len() != other_values.len() {
            return Err(PredicateError::InvalidBinding);
        }
        // Do not hide inconsistent actual aliases by widening their saved
        // facts. Reconcile each predecessor before forgetting path precision;
        // keep the original expressions rather than proof-query constants.
        self.check_local_parameter_captures(left, budget)?;
        other.check_local_parameter_captures(right, budget)?;
        let values = values
            .iter()
            .zip(&other_values)
            .map(|(a, b)| {
                let merged = if widen {
                    a.widen_capture(b, budget)
                } else {
                    a.join_capture(b, budget)
                };
                merged.map_err(|error| match error {
                    crate::predicate_logic::LogicError::Unbound => PredicateError::InvalidBinding,
                    other => logic::map_error(other),
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        // Private witnesses are forgotten by the caller. Retain only aliases
        // established above for public captures. A numeric name collision with
        // an old, unmapped snapshot cannot justify retaining its aliases.
        let used = logic::parameter_local_snapshots(&values, budget)?;
        aliases.retain(|_, snapshot| used.contains(snapshot));
        Ok(JoinedParameters { values, aliases })
    }
}
