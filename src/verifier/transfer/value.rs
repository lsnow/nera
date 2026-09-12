use super::*;

impl<'environment> TransferBuilder<'environment> {
    pub(super) fn check(&mut self, condition_id: VirValueId) -> Result<(), TransferError> {
        let condition = bool_fact(&self.state, condition_id)?;
        let status = if matches!(condition, AbstractBool::True)
            || self
                .state
                .path_condition()
                .implies(PathFact::boolean(condition_id, true))
        {
            ObligationStatus::Proven
        } else if matches!(condition, AbstractBool::False)
            || self
                .state
                .path_condition()
                .implies(PathFact::boolean(condition_id, false))
        {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::CheckTrue {
                condition: condition_id,
            },
            status,
        );
        // Like every fallible instruction, transfer describes the successful
        // continuation under its emitted obligation. The obligation remains
        // unresolved when the condition is unknown, so this refinement cannot
        // by itself make the enclosing sequence verified.
        self.state
            .conjoin_path_fact(PathFact::boolean(condition_id, true));
        Ok(())
    }
}
