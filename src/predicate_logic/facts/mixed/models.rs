//! Theory admission for finite Boolean models. This adapter owns neither
//! resource state nor a solver: it translates a candidate row into temporary
//! typed difference constraints and rejects only demonstrably impossible rows.
use super::*;

impl<T: Copy + Eq, A: Ord + Clone> MixedGraph<T, A> {
    pub(super) fn theory_forced(
        &self,
        queries: &[Literal],
        budget: &mut LogicBudget,
    ) -> Result<Vec<Option<bool>>, LogicError> {
        // Preserve the inexpensive propositional path. If it already forces
        // every result, a more precise model filter cannot add a conclusion.
        let values = if let [query] = queries {
            vec![self.booleans.forced(*query, budget)?]
        } else {
            self.booleans.forced_many(queries, budget)?
        };
        // Local propagation already checks each individual numeric observation.
        if self.observations.len() < 2 || values.iter().all(Option::is_some) {
            return Ok(values);
        }
        budget.charge(self.observations.len())?;
        let observations = self
            .observations
            .iter()
            .map(|(_, literal)| *literal)
            .collect::<Vec<_>>();
        self.booleans.forced_many_with_models(
            queries,
            &observations,
            budget,
            &mut |truths, budget| self.admit_numeric_model(truths, budget),
        )
    }

    fn admit_numeric_model(
        &self,
        truths: &[bool],
        budget: &mut LogicBudget,
    ) -> Result<bool, LogicError> {
        if truths.len() != self.observations.len() {
            return Err(LogicError::InvalidNode);
        }
        for ty in [LogicType::U64, LogicType::Usize] {
            if !self.observations.iter().any(|(n, _)| n.ty == ty) {
                continue;
            }
            let mut graph = self.numeric_graph(ty, budget)?;
            for ((numeric, _), truth) in self.observations.iter().zip(truths) {
                budget.charge(1)?;
                if numeric.ty == ty
                    && let Some(n) = Self::consequence(numeric, *truth)
                {
                    graph.comparison(n.op, &n.left, &n.right, budget)?;
                }
            }
            match graph.consistent(budget) {
                Ok(()) => {}
                Err(LogicError::Unproved) => return Ok(false),
                Err(error) => return Err(error),
            }
            for ((n, _), truth) in self.observations.iter().zip(truths) {
                budget.charge(1)?;
                // Disequality has two possible directions. Do not choose one:
                // reject it only when the remaining row proves equality.
                if n.ty == ty
                    && n.op == Comparison::Equal
                    && !truth
                    && graph.entails(Comparison::Equal, &n.left, &n.right, budget)?
                {
                    return Ok(false);
                }
            }
        }
        // A consistent difference abstraction is not a satisfiability proof.
        // Unknown models must survive, so they can only weaken conclusions.
        Ok(true)
    }
}
