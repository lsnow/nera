//! Read-only exact differences between typed, established word observations.
//! The result is a mathematical integer, not a machine subtraction result or
//! a runtime coordinate. Consumers separately admit sources and machine domains.
use super::*;

impl<T: Copy + Eq, A: Ord + Clone, R: Clone + Eq> EstablishedFacts<T, A, R> {
    pub(crate) fn exact_word_difference(
        &self,
        left: &TypedLogicValue<T, A, R>,
        right: &TypedLogicValue<T, A, R>,
        budget: &mut LogicBudget,
    ) -> Result<Option<i128>, LogicError> {
        budget.charge(1 + MAX_LINEAR_TERMS)?;
        validate_value(left, budget)?;
        validate_value(right, budget)?;
        if left.ty != right.ty || !matches!(left.ty, LogicType::U64 | LogicType::Usize) {
            return Err(LogicError::TypeMismatch);
        }
        let (LogicValue::Word(a), LogicValue::Word(b)) = (&left.value, &right.value) else {
            return Err(LogicError::TypeMismatch);
        };
        let a = LinearWord::from_word(a);
        let b = LinearWord::from_word(b);
        let mut graph = self.numeric_graph(left.ty, budget)?;
        // Keep both operand domains even if subtraction cancels every atom.
        // Conflicting copies must fail, not produce a vacuous zero difference.
        graph.word(&a, budget)?;
        graph.word(&b, budget)?;
        let difference = a.combine(&b, true)?;
        let (lower, upper) = graph.bounds(&difference, budget)?;
        Ok((lower == upper).then_some(lower))
    }
}
