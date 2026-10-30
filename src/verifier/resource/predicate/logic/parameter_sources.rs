//! Source admission for public capture alignment. This adapter reads actual
//! historical coordinates; pure scalar shapes never identify runtime slots.
use super::*;
use crate::predicate_logic::scalar_template::{ScalarKind, ScalarTemplate};

/// A predecessor's admitted sources and pending coordinate substitutions.
/// Keeping the source state here prevents mixing evidence from different edges.
pub(in crate::verifier::resource::predicate) struct ParameterAlignment<'a> {
    state: &'a ResourceState,
    instance: &'a PredicateInstance,
    atoms: BTreeMap<ObservationAtom, (ScalarCapture, ScalarKind)>,
    words: BTreeMap<ScalarCapture, AffineValue<ObservationAtom>>,
    public: BTreeSet<(ScalarCapture, ScalarKind)>,
    bindings: BTreeMap<ObservationAtom, VirValueId>,
    coordinates: Vec<(VirValueId, AffineValue<ObservationAtom>)>,
}

impl<'a> ParameterAlignment<'a> {
    pub(in crate::verifier::resource::predicate) fn new(
        state: &'a ResourceState,
        instance: &'a PredicateInstance,
        budget: &mut LogicBudget,
    ) -> Result<Self, PredicateError> {
        let atoms = parameter_scalar_sources(instance, budget)?;
        let words = state.parameter_word_coordinates(instance, &atoms, budget)?;
        let public = atoms
            .values()
            .copied()
            .chain(words.keys().map(|capture| (*capture, ScalarKind::Word)))
            .collect();
        Ok(Self {
            state,
            instance,
            atoms,
            words,
            public,
            bindings: BTreeMap::new(),
            coordinates: Vec::new(),
        })
    }

    pub(in crate::verifier::resource::predicate) fn contains(
        &self,
        capture: &(ScalarCapture, ScalarKind),
    ) -> bool {
        self.public.contains(capture)
    }

    /// The CFG caller establishes unique correspondence with the other edge.
    /// This adapter admits the predecessor's complete source representation.
    pub(in crate::verifier::resource::predicate) fn bind(
        &mut self,
        key: (ScalarCapture, ScalarKind),
        slot: VirValueId,
        budget: &mut LogicBudget,
    ) -> Result<(), PredicateError> {
        if !self.contains(&key) {
            return Err(PredicateError::InvalidBinding);
        }
        let mut atomic = false;
        for (atom, capture) in &self.atoms {
            budget.charge(1).map_err(map_error)?;
            if *capture == key {
                self.bindings.insert(atom.clone(), slot);
                atomic = true;
            }
        }
        if !atomic {
            // Reconcile every surviving copy, including copies in private slots.
            self.state
                .current_scalar_capture(self.instance, key.0, key.1, budget)
                .map_err(map_error)?;
            let word = self
                .words
                .get(&key.0)
                .ok_or(PredicateError::InvalidBinding)?;
            self.coordinates.push((slot, word.clone()));
        }
        Ok(())
    }

    pub(in crate::verifier::resource::predicate) fn normalize(
        &self,
        target: InstanceScope,
        budget: &mut LogicBudget,
    ) -> Result<Vec<PredicateLogicValue>, PredicateError> {
        identity::normalize_closed_parameters_with_coordinates(
            self.instance,
            target,
            &self.bindings,
            &self.coordinates,
            budget,
        )
    }
}

fn parameter_scalar_sources(
    instance: &PredicateInstance,
    budget: &mut LogicBudget,
) -> Result<BTreeMap<ObservationAtom, (ScalarCapture, ScalarKind)>, PredicateError> {
    if instance.logical_parameters.len() > MAX_LOGIC_PARAMETERS {
        return Err(PredicateError::Budget);
    }
    let scope = instance.logic_scope.ok_or(PredicateError::InvalidBinding)?;
    let mut sources = BTreeMap::new();
    for value in &instance.logical_parameters {
        budget.charge(1).map_err(map_error)?;
        if matches!(value.ty, LogicType::Resource(_)) {
            continue;
        }
        ScalarTemplate::capture(
            &value.value,
            &mut |atom, kind, _| {
                let local_scope = match atom {
                    ObservationAtom::Historical {
                        scope: captured, ..
                    }
                    | ObservationAtom::HistoricalBool {
                        scope: captured, ..
                    } => *captured == scope,
                    _ => true,
                };
                if local_scope
                    && let Some(capture) = ScalarCapture::from_atom(atom, kind)
                    && sources
                        .insert(atom.clone(), (capture, kind))
                        .is_some_and(|previous| previous != (capture, kind))
                {
                    return Err(LogicError::TypeMismatch);
                }
                Ok(atom.clone())
            },
            budget,
        )
        .map_err(map_error)?;
    }
    Ok(sources)
}

impl ResourceState {
    /// Full live word sources whose roots occur in public captures. The pure
    /// rebaser still requires each chosen source's support in the operand it
    /// rewrites; membership here alone never identifies a root with a slot.
    fn parameter_word_coordinates(
        &self,
        instance: &PredicateInstance,
        atoms: &BTreeMap<ObservationAtom, (ScalarCapture, ScalarKind)>,
        budget: &mut LogicBudget,
    ) -> Result<BTreeMap<ScalarCapture, AffineValue<ObservationAtom>>, PredicateError> {
        let mut result = BTreeMap::new();
        for value in &instance.logical_parameters {
            for (capture, word) in self.predicate_capture_word_sources(instance, value, budget)? {
                budget.charge(word.terms.len()).map_err(map_error)?;
                if word.terms.keys().all(|atom| {
                    atoms
                        .get(atom)
                        .is_some_and(|(_, kind)| *kind == ScalarKind::Word)
                }) {
                    result.insert(capture, word);
                }
            }
        }
        Ok(result)
    }

    /// Same preference as actual scalar capture: complete checked provenance,
    /// then a surviving local alias. A composite word never names just its root.
    pub(in crate::verifier::resource::predicate) fn predicate_slot_capture(
        &self,
        instance: &PredicateInstance,
        slot: VirValueId,
    ) -> Option<(ScalarCapture, ScalarKind)> {
        let (origin, kind) = match self.value(slot)? {
            AbstractValue::U64(_) => (
                self.word_origin(slot).map(ScalarCapture::Word),
                ScalarKind::Word,
            ),
            AbstractValue::Bool(_) => (
                self.bool_origin(slot).map(ScalarCapture::Bool),
                ScalarKind::Bool,
            ),
            _ => return None,
        };
        let capture = origin.or_else(|| {
            instance
                .logical_local_aliases
                .get(&slot)
                .copied()
                .map(ScalarCapture::Local)
        })?;
        Some((capture, kind))
    }
}
