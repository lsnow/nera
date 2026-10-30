//! Typed symbolic forms occurring in established numeric premises. A candidate
//! is not an equality, a runtime coordinate, or permission to observe storage.
//! Consumers must separately prove their query and admit every actual source.
use super::*;

impl<T: Copy + Eq, A: Ord + Clone, R: Clone + Eq> EstablishedFacts<T, A, R> {
    pub(crate) fn symbolic_word_candidates(
        &self,
        ty: LogicType<T>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<TypedLogicValue<T, A, R>>, LogicError> {
        budget.charge(1)?;
        if !matches!(ty, LogicType::U64 | LogicType::Usize) {
            return Err(LogicError::TypeMismatch);
        }
        let mut graph = self.constraint_graph(&[], budget)?;
        graph.propagate(budget)?;
        let mut shapes = BTreeMap::<(i128, BTreeMap<A, i128>), LinearWord<A>>::new();
        for (_, left, right) in graph.numeric_premises(ty, budget)? {
            for word in [left, right] {
                budget.charge(1 + word.terms.len())?;
                if word.terms.is_empty() {
                    continue;
                }
                let entry = shapes
                    .entry((word.constant, word.terms.clone()))
                    .or_insert(word.clone());
                entry.lower = entry.lower.max(word.lower);
                entry.upper = entry.upper.min(word.upper);
                if entry.lower > entry.upper {
                    return Err(LogicError::Unproved);
                }
                if shapes.len() > MAX_EXPRESSION_NODES {
                    return Err(LogicError::Budget);
                }
            }
        }
        let mut candidates = Vec::new();
        for (_, mut word) in shapes {
            // These are candidates, not requested tight bounds. Avoid solving
            // every already machine-defined form before the consumer selects
            // one. Refine only when mathematical bounds do not fit a word.
            if word.clone().into_word().is_err() {
                graph.refine_word(ty, &mut word, budget)?;
            }
            let word = match word.into_word() {
                Ok(word) => word,
                // A mathematical premise need not be a machine expression.
                // Omit undefined forms rather than claim a wrapping result.
                Err(LogicError::Overflow) => continue,
                Err(error) => return Err(error),
            };
            candidates.push(TypedLogicValue {
                ty,
                value: LogicValue::Word(word),
            });
        }
        Ok(candidates)
    }
}
