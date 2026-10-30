//! Translate current numeric facts through actual scalar observations supplied
//! by the caller. This bridge never imports a package's pending guarantee.
use super::*;
use crate::predicate_logic::facts::{DifferenceObservation, EstablishedFacts};
pub(super) type ScalarDifference =
    DifferenceObservation<VirMemoryAccess, ObservationAtom, ResourceWitness>;

impl ResourceState {
    pub(in crate::verifier::resource::predicate) fn predicate_scalar_relations(
        &self,
        inputs: &BTreeMap<VirValueId, PredicateLogicValue>,
        budget: &mut LogicBudget,
    ) -> Result<EstablishedFacts<VirMemoryAccess, ObservationAtom, ResourceWitness>, PredicateError>
    {
        let mut facts = EstablishedFacts::new();
        let differences = self.predicate_scalar_differences(inputs, budget)?;
        facts
            .extend_observations(&[], &differences, budget)
            .map_err(map_error)?;
        Ok(facts)
    }

    pub(super) fn predicate_scalar_differences(
        &self,
        inputs: &BTreeMap<VirValueId, PredicateLogicValue>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<ScalarDifference>, PredicateError> {
        let mut differences = Vec::new();
        for bound in self.relations.bounds() {
            budget.charge(1).map_err(map_error)?;
            let left = bound.left.and_then(|id| inputs.get(&id));
            let right = bound.right.and_then(|id| inputs.get(&id));
            // Missing endpoints do not name an existential, a zero, or a
            // similarly bounded value. Closed relation chains are exported by
            // the numeric component, never reconstructed with guessed leaves.
            if bound.left.is_some() && left.is_none() || bound.right.is_some() && right.is_none() {
                continue;
            }
            let Some(ty) = left.or(right).map(|v| v.ty) else {
                continue;
            };
            if !matches!(ty, LogicType::U64 | LogicType::Usize)
                || left.is_some_and(|v| v.ty != ty)
                || right.is_some_and(|v| v.ty != ty)
            {
                continue;
            }
            let zero = TypedLogicValue {
                ty,
                value: LogicValue::Word(AffineValue::exact(0)),
            };
            differences.push((
                left.unwrap_or(&zero).clone(),
                right.unwrap_or(&zero).clone(),
                bound.bound,
            ));
        }
        Ok(differences)
    }
}
