//! Actual identity evidence for scalar captures. Pure expression templates do
//! not choose SSA slots; loop adapters do not interpret historical coordinates.
use super::*;
use crate::predicate_logic::scalar_template::ScalarKind;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::verifier::resource::predicate) enum ScalarCapture {
    Local(LocalSnapshot),
    Word(ScalarOrigin),
    Bool(BoolOrigin),
}

impl ScalarCapture {
    pub(in crate::verifier::resource::predicate) fn from_atom(
        atom: &ObservationAtom,
        kind: ScalarKind,
    ) -> Option<Self> {
        match (atom, kind) {
            (ObservationAtom::Local { scope, value }, _) => Some(Self::Local(LocalSnapshot {
                scope: *scope,
                value: *value,
            })),
            (
                ObservationAtom::Historical {
                    cell, local: true, ..
                },
                ScalarKind::Word,
            ) => Some(Self::Word(ScalarOrigin {
                first: *cell,
                scale: 1,
                second: None,
                addend: 0,
            })),
            (
                ObservationAtom::HistoricalBool {
                    origin,
                    local: true,
                    ..
                },
                ScalarKind::Bool,
            ) => Some(Self::Bool(*origin)),
            // Foreign/captured histories do not belong to this frame. Neither
            // current addresses nor a matching range reattach them to a slot.
            _ => None,
        }
    }
}

impl ResourceState {
    pub(in crate::verifier::resource::predicate) fn predicate_capture_matches(
        &self,
        instance: &PredicateInstance,
        capture: ScalarCapture,
        slot: VirValueId,
        kind: ScalarKind,
    ) -> bool {
        if !matches!(
            (kind, self.value(slot)),
            (ScalarKind::Word, Some(AbstractValue::U64(_)))
                | (ScalarKind::Bool, Some(AbstractValue::Bool(_)))
        ) {
            return false;
        }
        match (capture, kind) {
            (ScalarCapture::Local(snapshot), _) => {
                instance.logical_local_aliases.get(&slot) == Some(&snapshot)
            }
            (ScalarCapture::Word(origin), ScalarKind::Word) => {
                self.word_origin(slot) == Some(origin)
            }
            (ScalarCapture::Bool(origin), ScalarKind::Bool) => {
                self.bool_origin(slot) == Some(origin)
            }
            _ => false,
        }
    }

    pub(in crate::verifier::resource::predicate) fn read_predicate_capture(
        &self,
        instance: &PredicateInstance,
        capture: ScalarCapture,
        slot: VirValueId,
        ty: LogicType<VirMemoryAccess>,
        budget: &mut LogicBudget,
    ) -> Result<PredicateLogicValue, PredicateError> {
        budget.charge(1).map_err(map_error)?;
        let kind = match ty {
            LogicType::U64 | LogicType::Usize => ScalarKind::Word,
            LogicType::Bool => ScalarKind::Bool,
            _ => return Err(PredicateError::InvalidBinding),
        };
        if !self.predicate_capture_matches(instance, capture, slot, kind) {
            return Err(PredicateError::InvalidBinding);
        }
        Ok(TypedLogicValue {
            ty,
            value: self
                .current_scalar_capture(instance, capture, kind, budget)
                .map_err(map_error)?,
        })
    }

    pub(super) fn current_scalar_capture(
        &self,
        instance: &PredicateInstance,
        capture: ScalarCapture,
        kind: ScalarKind,
        budget: &mut LogicBudget,
    ) -> Result<LogicValue<ObservationAtom, ResourceWitness>, LogicError> {
        if instance.logical_local_aliases.len() > MAX_PREDICATE_LOCAL_ALIASES {
            return Err(LogicError::Budget);
        }
        let mut ids = Vec::new();
        match capture {
            ScalarCapture::Local(snapshot) => {
                for (id, alias) in &instance.logical_local_aliases {
                    budget.charge(1)?;
                    if *alias == snapshot {
                        ids.push(*id);
                    }
                }
            }
            ScalarCapture::Word(expected) => {
                for (id, origin) in &self.word_origins {
                    budget.charge(1)?;
                    if *origin == expected {
                        ids.push(*id);
                    }
                }
            }
            ScalarCapture::Bool(origin) => {
                for (id, candidate) in &self.bool_origins {
                    budget.charge(1)?;
                    if *candidate == origin {
                        ids.push(*id);
                    }
                }
            }
        }
        if ids.is_empty() {
            return Err(LogicError::Unbound);
        }
        let (mut lower, mut upper) = (0, u64::MAX);
        let mut boolean = None;
        for id in ids {
            budget.charge(1)?;
            match (kind, self.value(id)) {
                (ScalarKind::Word, Some(AbstractValue::U64(value))) => {
                    lower = lower.max(value.lower());
                    upper = upper.min(value.upper());
                    if lower > upper {
                        return Err(LogicError::Unproved);
                    }
                }
                (ScalarKind::Bool, Some(AbstractValue::Bool(value))) => {
                    let known = match value {
                        AbstractBool::True => Some(true),
                        AbstractBool::False => Some(false),
                        AbstractBool::Unknown => None,
                    };
                    if let Some(known) = known {
                        if boolean.is_some_and(|previous| previous != known) {
                            return Err(LogicError::Unproved);
                        }
                        boolean = Some(known);
                    }
                }
                (_, None) => return Err(LogicError::Unbound),
                _ => return Err(LogicError::TypeMismatch),
            }
        }
        match (capture, kind) {
            (ScalarCapture::Local(snapshot), ScalarKind::Word) => Ok(LogicValue::Word(
                AffineValue::identified(snapshot.atom(), lower, upper)?,
            )),
            (ScalarCapture::Local(snapshot), ScalarKind::Bool) => Ok(LogicValue::BoolAtom {
                atom: snapshot.atom(),
                negated: false,
                known: boolean,
            }),
            (ScalarCapture::Word(origin), ScalarKind::Word) => {
                let scope = instance.logic_scope.ok_or(LogicError::Unbound)?;
                let interval = U64Interval::new(lower, upper).map_err(|_| LogicError::Unproved)?;
                Ok(LogicValue::Word(observations::observed_scalar_word(
                    scope,
                    interval,
                    Some(origin),
                    ObservationAtom::Historical {
                        scope,
                        cell: origin.first,
                        local: true,
                    },
                )?))
            }
            (ScalarCapture::Bool(origin), ScalarKind::Bool) => {
                let scope = instance.logic_scope.ok_or(LogicError::Unbound)?;
                let value = boolean.map_or(AbstractBool::Unknown, |b| {
                    if b {
                        AbstractBool::True
                    } else {
                        AbstractBool::False
                    }
                });
                Ok(observations::observed_scalar_bool(
                    scope,
                    value,
                    Some(origin),
                    None,
                ))
            }
            _ => Err(LogicError::TypeMismatch),
        }
    }
}
