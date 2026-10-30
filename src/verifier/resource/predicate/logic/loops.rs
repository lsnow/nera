//! Existential abstraction for a checked, sealed loop package. Resource frame
//! admission belongs to the parent adapter; this never creates runtime facts.
use super::*;

impl ResourceState {
    pub(in crate::verifier::resource::predicate) fn abstract_loop_predicate_logic(
        &self,
        instance: &mut PredicateInstance,
        next: &mut u64,
        budget: &mut LogicBudget,
    ) -> Result<(), PredicateError> {
        if instance.logic_scope.is_none() {
            return Ok(());
        }
        let scope = InstanceScope {
            declaration: instance.definition.id.get(),
            instance: *next,
            opening: 0,
        };
        let following = next.checked_add(1).ok_or(PredicateError::Budget)?;
        *instance = self.abstract_predicate_logic_at_scope(instance, scope, budget)?;
        *next = following;
        Ok(())
    }
}
