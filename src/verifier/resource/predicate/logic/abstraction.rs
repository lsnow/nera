//! Forget particular witnesses of an already established existential package.
//! Callers admit real resources and select the namespace. This adapter reads
//! actual observations; pure constraint reasoning remains in predicate_logic.
use super::*;

impl ResourceState {
    /// Rebuild only the declaration's existential guarantee. The caller must
    /// establish the old package and preserve its public parameters, or supply
    /// separately checked inductive parameter bindings. Neither
    /// initialization nor authority nor observation origins are created here.
    /// CFG/loop frame adapters separately decide which SSA aliases survive.
    pub(in crate::verifier::resource::predicate) fn abstract_predicate_logic_at_scope(
        &self,
        instance: &PredicateInstance,
        scope: InstanceScope,
        budget: &mut LogicBudget,
    ) -> Result<PredicateInstance, PredicateError> {
        if !instance.folded
            || instance.opening_action.is_some()
            || !instance.borrowed_by.is_empty()
            || instance.logic_scope.is_none()
            || scope.opening != 0
            || scope.declaration != instance.definition.id.get()
        {
            return Err(PredicateError::InvalidBinding);
        }
        let mut result = instance.clone();
        for parameter in &mut result.logical_parameters {
            budget.charge(1).map_err(map_error)?;
            rebind_local_origins(parameter, scope, budget).map_err(map_error)?;
        }
        let definition = &instance.definition;
        let witnesses = self.import_predicate_witnesses(
            definition,
            &result.logical_parameters,
            scope,
            &mut |r, o, a, t| {
                self.observe_predicate_logic(
                    definition,
                    &instance.resources,
                    scope,
                    true,
                    (r, o, a, t),
                )
            },
            &mut |r, path| resource_value(self, definition, &instance.resources, r, path),
            budget,
        )?;
        // Existential abstraction discards facts specific to the old witness.
        // Only the declaration proven for the admitted package is retained.
        let facts = self.capture_predicate_constraints(
            definition,
            &instance.resources,
            scope,
            &result.logical_parameters,
            &witnesses,
            &[],
            true,
            None,
            budget,
        )?;
        result.logic_scope = Some(scope);
        result.logical_witnesses = witnesses;
        result.logical_facts = facts;
        // Initialization is part of the already established existential
        // package. Forget the old endpoint together with its constraints and
        // instantiate that same clause for the new witness; copying just the
        // old endpoint (or dropping the clause) breaks the package invariant.
        result.logical_initialization =
            self.abstract_predicate_logical_prefixes(&result, budget)?;
        Ok(result)
    }
}
