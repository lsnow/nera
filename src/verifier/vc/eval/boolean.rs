//! Finite Boolean propagation over query-local immutable identities. The
//! boundary adapter owns identity assignment; this evaluator sees no memory.
use super::{AbstractBool, PureValue, bool_value, equal, numeric};

pub(super) fn not(value: PureValue) -> PureValue {
    match value {
        PureValue::BooleanIdentity {
            identity,
            negated,
            known,
        } => PureValue::BooleanIdentity {
            identity,
            negated: !negated,
            known: numeric::not(known),
        },
        _ => PureValue::Bool(numeric::not(bool_value(value))),
    }
}

pub(super) fn junction(values: Vec<PureValue>, disjunction: bool) -> PureValue {
    let neutral = if disjunction {
        AbstractBool::False
    } else {
        AbstractBool::True
    };
    let decisive = numeric::not(neutral);
    let mut retained = None;
    let mut distinct = false;
    for value in values {
        match bool_value(value) {
            known if known == decisive => return PureValue::Bool(decisive),
            known if known == neutral => continue,
            _ => {}
        }
        if let Some(previous) = retained {
            match equal(previous, value) {
                AbstractBool::True => {}
                AbstractBool::False => return PureValue::Bool(decisive),
                AbstractBool::Unknown => distinct = true,
            }
        } else {
            retained = Some(value);
        }
    }
    if distinct {
        PureValue::Bool(AbstractBool::Unknown)
    } else {
        retained.unwrap_or(PureValue::Bool(neutral))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn symbol(identity: u32, negated: bool) -> PureValue {
        PureValue::BooleanIdentity {
            identity,
            negated,
            known: AbstractBool::Unknown,
        }
    }
    fn model(value: PureValue, assignment: u32, unknown: bool) -> bool {
        match value {
            PureValue::Bool(AbstractBool::True) => true,
            PureValue::Bool(AbstractBool::False) => false,
            PureValue::Bool(AbstractBool::Unknown) => unknown,
            PureValue::BooleanIdentity {
                identity, negated, ..
            } => ((assignment >> identity) & 1 != 0) ^ negated,
            _ => panic!("Boolean operand"),
        }
    }
    fn permits(value: PureValue, assignment: u32, actual: bool) -> bool {
        value == PureValue::Bool(AbstractBool::Unknown)
            || model(value, assignment, actual) == actual
    }

    #[test]
    fn boolean_identity_operations_are_sound_for_all_small_models() {
        let values = [
            PureValue::Bool(AbstractBool::False),
            PureValue::Bool(AbstractBool::True),
            PureValue::Bool(AbstractBool::Unknown),
            symbol(0, false),
            symbol(0, true),
            symbol(1, false),
            symbol(1, true),
        ];
        for a in values {
            for b in values {
                for c in values {
                    for model_id in 0..32 {
                        let aa = model(a, model_id, model_id & 4 != 0);
                        let bb = model(b, model_id, model_id & 8 != 0);
                        let cc = model(c, model_id, model_id & 16 != 0);
                        assert!(permits(not(a), model_id, !aa));
                        assert!(permits(PureValue::Bool(equal(a, b)), model_id, aa == bb));
                        assert!(permits(
                            junction(vec![a, b, c], false),
                            model_id,
                            aa && bb && cc
                        ));
                        assert!(permits(
                            junction(vec![a, b, c], true),
                            model_id,
                            aa || bb || cc
                        ));
                    }
                }
            }
        }
        assert_eq!(
            equal(symbol(0, false), not(not(symbol(0, false)))),
            AbstractBool::True
        );
        assert_eq!(
            equal(symbol(0, false), symbol(1, false)),
            AbstractBool::Unknown
        );
        assert_eq!(
            junction(vec![symbol(0, false), symbol(0, true)], false),
            PureValue::Bool(AbstractBool::False)
        );
    }
}
