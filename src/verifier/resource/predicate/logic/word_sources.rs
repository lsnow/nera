//! Supply complete current-frame affine sources to the pure template adapter.
//! Never infer a root slot by dividing an origin or by matching numeric ranges.
use super::*;

impl ResourceState {
    pub(in crate::verifier::resource::predicate) fn predicate_word_sources(
        &self,
        instance: &PredicateInstance,
        slots: &BTreeSet<VirValueId>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<(VirValueId, ScalarOrigin, AffineValue<ObservationAtom>)>, PredicateError> {
        let Some(scope) = instance.logic_scope else {
            return Ok(Vec::new());
        };
        let mut sources = Vec::new();
        for slot in slots {
            budget.charge(1).map_err(map_error)?;
            let Some(origin) = self.word_origin(*slot) else {
                continue;
            };
            if !matches!(self.value(*slot), Some(AbstractValue::U64(_))) {
                continue;
            }
            let value = self.predicate_scalar_input(
                scope,
                LogicType::U64,
                *slot,
                &instance.logical_local_aliases,
            )?;
            let LogicValue::Word(word) = value.value else {
                return Err(PredicateError::InvalidBinding);
            };
            budget.charge(word.terms.len()).map_err(map_error)?;
            // Actual origins retain identity even when their bounds are exact.
            // A purely constant origin without symbolic terms is not an input.
            if !word.terms.is_empty()
                && word
                    .terms
                    .keys()
                    .all(|atom| matches!(atom, ObservationAtom::Historical { local: true, .. }))
            {
                sources.push((*slot, origin, word));
            }
        }
        Ok(sources)
    }
    /// Immutable copies of one complete origin select a deterministic live
    /// representative; reading the capture still reconciles every actual copy.
    pub(in crate::verifier::resource::predicate) fn predicate_retained_word_sources(
        &self,
        instance: &PredicateInstance,
        slots: &BTreeSet<VirValueId>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<(VirValueId, ScalarCapture, AffineValue<ObservationAtom>)>, PredicateError>
    {
        let mut sources = BTreeMap::new();
        for (slot, origin, word) in self.predicate_word_sources(instance, slots, budget)? {
            budget.charge(1).map_err(map_error)?;
            sources.entry(origin).or_insert((slot, word));
        }
        Ok(sources
            .into_iter()
            .map(|(origin, (slot, word))| (slot, ScalarCapture::Word(origin), word))
            .collect())
    }

    /// Capture refinement reads only complete sources for local historical
    /// roots present in this value. A boolean/foreign-only value must not scan
    /// or depend on unrelated word state.
    pub(super) fn predicate_capture_word_sources(
        &self,
        instance: &PredicateInstance,
        value: &PredicateLogicValue,
        budget: &mut LogicBudget,
    ) -> Result<Vec<(ScalarCapture, AffineValue<ObservationAtom>)>, PredicateError> {
        let mut words = Vec::new();
        for leaf in value.value.capture_leaves(budget).map_err(map_error)? {
            match leaf {
                LogicValue::Word(word) => words.push(word),
                LogicValue::BoolComparison { left, right, .. } => words.extend([left, right]),
                _ => {}
            }
        }
        let mut cells = BTreeSet::new();
        for word in words {
            budget.charge(word.terms.len()).map_err(map_error)?;
            for atom in word.terms.keys() {
                if let ObservationAtom::Historical {
                    cell, local: true, ..
                } = atom
                {
                    cells.insert(*cell);
                }
            }
        }
        if cells.is_empty() {
            return Ok(Vec::new());
        }
        let mut slots = BTreeSet::new();
        for (slot, origin) in &self.word_origins {
            budget.charge(1).map_err(map_error)?;
            if origin
                .terms()
                .all(|(cell, coefficient)| coefficient == 0 || cells.contains(&cell))
            {
                slots.insert(*slot);
            }
        }
        Ok(self
            .predicate_retained_word_sources(instance, &slots, budget)?
            .into_iter()
            .map(|(_, capture, word)| (capture, word))
            .collect())
    }
}
