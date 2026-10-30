//! Refine immutable current-frame captures through actual surviving sources.
//! Local aliases and historical roots may occur in the same expression. Numeric
//! bounds are consequences of that identity, never a substitute for it.
use super::*;
use crate::predicate_logic::scalar_template::ScalarTemplate;

impl ResourceState {
    /// Validate live immutable captures before an adapter forgets precision.
    /// Discard query refinements: a known truth must not erase the shape used
    /// to align public parameters on both predecessors.
    pub(in crate::verifier::resource::predicate) fn check_local_parameter_captures(
        &self,
        instance: &PredicateInstance,
        budget: &mut LogicBudget,
    ) -> Result<(), PredicateError> {
        budget
            .charge(instance.logical_parameters.len())
            .map_err(map_error)?;
        if instance.logical_parameters.len() > MAX_LOGIC_PARAMETERS {
            return Err(PredicateError::Budget);
        }
        for value in &instance.logical_parameters {
            self.refine_local_capture(instance, value.clone(), budget)?;
        }
        Ok(())
    }

    pub(super) fn refine_local_capture(
        &self,
        instance: &PredicateInstance,
        value: PredicateLogicValue,
        budget: &mut LogicBudget,
    ) -> Result<PredicateLogicValue, PredicateError> {
        if let LogicValue::BoolBinary {
            operation,
            left,
            right,
            negated,
        } = &value.value
        {
            value.value.capture_leaves(budget).map_err(map_error)?;
            // Check each saved leaf, not just the final truth: an annihilator
            // must not hide a stale/conflicting live capture elsewhere inside.
            let left = self.refine_local_capture(
                instance,
                TypedLogicValue {
                    ty: value.ty,
                    value: *left.clone(),
                },
                budget,
            )?;
            let right = self.refine_local_capture(
                instance,
                TypedLogicValue {
                    ty: value.ty,
                    value: *right.clone(),
                },
                budget,
            )?;
            return Ok(TypedLogicValue {
                ty: value.ty,
                value: LogicValue::boolean_binary(
                    *operation,
                    left.value,
                    right.value,
                    *negated,
                    budget,
                )
                .map_err(map_error)?,
            });
        }
        let sources = self.predicate_capture_word_sources(instance, &value, budget)?;
        let template = ScalarTemplate::capture_rebased(
            &value.value,
            &[],
            &sources,
            &mut |atom, kind, _| ScalarCapture::from_atom(atom, kind).ok_or(LogicError::Unbound),
            budget,
        );
        let template = match template {
            Ok(template) => template,
            Err(LogicError::Unbound) => return Ok(value),
            Err(error) => return Err(map_error(error)),
        };
        if template.inputs(budget).map_err(map_error)?.is_empty() {
            return Ok(value);
        }
        let refined = template.instantiate(
            &mut |capture, kind, budget| {
                self.current_scalar_capture(instance, *capture, kind, budget)
            },
            budget,
        );
        let mut refined = match refined {
            Ok(refined) => refined,
            // A wider current abstraction need not recover the capture's
            // original domain. Keep that immutable value without new evidence.
            Err(LogicError::Unbound | LogicError::Overflow) => return Ok(value),
            Err(error) => return Err(map_error(error)),
        };
        if let (LogicValue::Word(old), LogicValue::Word(new)) = (&value.value, &mut refined) {
            new.lower = new.lower.max(old.lower);
            new.upper = new.upper.min(old.upper);
            if new.lower > new.upper {
                return Err(PredicateError::UnprovedRepresentation);
            }
        }
        if let (Some(old), Some(current)) = (value.value.known_boolean(), refined.known_boolean())
            && old != current
        {
            return Err(PredicateError::UnprovedRepresentation);
        }
        if matches!(refined, LogicValue::BoolAtom { .. }) {
            // Actual source reconciliation above admits this immutable truth.
            // The pure value service checks consistency and preserves identity.
            if let Some(old) = value.value.known_boolean() {
                refined = refined.with_known_boolean(old).map_err(map_error)?;
            }
        }
        Ok(TypedLogicValue {
            ty: value.ty,
            value: refined,
        })
    }
}
