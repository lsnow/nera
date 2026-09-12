use std::collections::{BTreeMap, BTreeSet};

use crate::{VirFunction, VirSpecSnapshot};

use super::super::resource::{AbstractBool, AbstractValue, PathFact, ResourceState, U64Interval};
use super::arena::{VcArena, VcLimits, VcTerm, VcTermId};

#[derive(Clone, Copy)]
pub(in crate::verifier) enum SnapshotValues<'a> {
    State(&'a ResourceState),
    Results(&'a [AbstractValue]),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PureValue {
    Bool(AbstractBool),
    U64(U64Interval),
}

/// Shared budget for every VC query performed while proving one function.
pub(in crate::verifier) struct VcQueryBudget {
    remaining_queries: usize,
    remaining_steps: usize,
}

impl VcQueryBudget {
    pub(in crate::verifier) const fn new(limits: VcLimits) -> Self {
        Self {
            remaining_queries: limits.max_queries,
            remaining_steps: limits.max_query_steps,
        }
    }

    fn begin_query(&mut self) -> Option<()> {
        self.remaining_queries = self.remaining_queries.checked_sub(1)?;
        Some(())
    }

    fn charge(&mut self, amount: usize) -> Option<()> {
        self.remaining_steps = self.remaining_steps.checked_sub(amount)?;
        Some(())
    }
}

/// Evaluates a normalized VC without host recursion. Any exhausted budget or
/// malformed arena edge produces `None`, which the caller maps to Unknown.
pub(in crate::verifier) fn evaluate_bool(
    arena: &VcArena,
    root: VcTermId,
    trusted: &BTreeSet<VcTermId>,
    values: SnapshotValues<'_>,
    function: &VirFunction,
    budget: &mut VcQueryBudget,
) -> Option<AbstractBool> {
    budget.begin_query()?;
    arena.get(root)?;
    let mut evaluated = BTreeMap::new();
    let mut stack = vec![(root, false)];

    while let Some((id, expanded)) = stack.pop() {
        if evaluated.contains_key(&id) {
            continue;
        }
        if trusted.contains(&id) {
            evaluated.insert(id, PureValue::Bool(AbstractBool::True));
            continue;
        }
        let term = arena.get(id)?;
        if !expanded {
            budget.charge(1usize.saturating_add(term.child_count()))?;
            stack.push((id, true));
            for child_index in (0..term.child_count()).rev() {
                let child = term.child_at(child_index)?;
                arena.get(child)?;
                if !evaluated.contains_key(&child) {
                    stack.push((child, false));
                }
            }
            continue;
        }

        evaluated.insert(id, evaluate_node(term, &evaluated, values, function)?);
    }

    evaluated.get(&root).copied().map(bool_value)
}

fn evaluate_node(
    term: &VcTerm,
    evaluated: &BTreeMap<VcTermId, PureValue>,
    values: SnapshotValues<'_>,
    function: &VirFunction,
) -> Option<PureValue> {
    let child = |id: VcTermId| evaluated.get(&id).copied();
    Some(match term {
        VcTerm::Bool(value) => PureValue::Bool(if *value {
            AbstractBool::True
        } else {
            AbstractBool::False
        }),
        VcTerm::U64(value) => PureValue::U64(U64Interval::exact(*value)),
        VcTerm::Binder(_) => PureValue::Bool(AbstractBool::Unknown),
        VcTerm::Snapshot(snapshot) => snapshot_value(*snapshot, values, function),
        VcTerm::Equal(left, right) => {
            if left == right {
                PureValue::Bool(AbstractBool::True)
            } else {
                PureValue::Bool(equal(child(*left)?, child(*right)?))
            }
        }
        VcTerm::LessThan(left, right) => {
            PureValue::Bool(compare(child(*left)?, child(*right)?, false))
        }
        VcTerm::LessOrEqual(left, right) => {
            PureValue::Bool(compare(child(*left)?, child(*right)?, true))
        }
        VcTerm::Not(operand) => PureValue::Bool(match bool_value(child(*operand)?) {
            AbstractBool::True => AbstractBool::False,
            AbstractBool::False => AbstractBool::True,
            AbstractBool::Unknown => AbstractBool::Unknown,
        }),
        VcTerm::And(operands) => PureValue::Bool(eval_and(
            operands
                .iter()
                .map(|operand| child(*operand).map(bool_value))
                .collect::<Option<Vec<_>>>()?
                .into_iter(),
        )),
        VcTerm::Or(operands) => PureValue::Bool(eval_or(
            operands
                .iter()
                .map(|operand| child(*operand).map(bool_value))
                .collect::<Option<Vec<_>>>()?
                .into_iter(),
        )),
    })
}

fn snapshot_value(
    snapshot: VirSpecSnapshot,
    values: SnapshotValues<'_>,
    function: &VirFunction,
) -> PureValue {
    let value = match (snapshot, values) {
        (
            VirSpecSnapshot::Parameter {
                function: owner,
                slot,
            },
            SnapshotValues::State(state),
        ) if owner == function.id => function
            .blocks
            .iter()
            .find(|block| block.id == function.entry)
            .and_then(|block| block.parameters.get(slot as usize))
            .and_then(|parameter| state.value(parameter.id))
            .copied(),
        (
            VirSpecSnapshot::Result {
                function: owner,
                slot,
            },
            SnapshotValues::Results(results),
        ) if owner == function.id => results.get(slot as usize).copied(),
        (
            VirSpecSnapshot::Value {
                function: owner,
                value,
            },
            SnapshotValues::State(state),
        ) if owner == function.id => state.value(value).copied().map(|abstract_value| {
            if abstract_value == AbstractValue::Bool(AbstractBool::Unknown)
                && state
                    .path_condition()
                    .implies(PathFact::boolean(value, true))
            {
                AbstractValue::Bool(AbstractBool::True)
            } else if abstract_value == AbstractValue::Bool(AbstractBool::Unknown)
                && state
                    .path_condition()
                    .implies(PathFact::boolean(value, false))
            {
                AbstractValue::Bool(AbstractBool::False)
            } else {
                abstract_value
            }
        }),
        _ => None,
    };
    match value {
        Some(AbstractValue::Bool(value)) => PureValue::Bool(value),
        Some(AbstractValue::U64(value)) => PureValue::U64(value),
        _ => PureValue::Bool(AbstractBool::Unknown),
    }
}

const fn bool_value(value: PureValue) -> AbstractBool {
    match value {
        PureValue::Bool(value) => value,
        PureValue::U64(_) => AbstractBool::Unknown,
    }
}

fn equal(left: PureValue, right: PureValue) -> AbstractBool {
    match (left, right) {
        (PureValue::Bool(left), PureValue::Bool(right)) => match (left, right) {
            (AbstractBool::True, AbstractBool::True)
            | (AbstractBool::False, AbstractBool::False) => AbstractBool::True,
            (AbstractBool::True, AbstractBool::False)
            | (AbstractBool::False, AbstractBool::True) => AbstractBool::False,
            _ => AbstractBool::Unknown,
        },
        (PureValue::U64(left), PureValue::U64(right)) => {
            if left.upper() < right.lower() || right.upper() < left.lower() {
                AbstractBool::False
            } else if left.exact_value() == right.exact_value() && left.exact_value().is_some() {
                AbstractBool::True
            } else {
                AbstractBool::Unknown
            }
        }
        _ => AbstractBool::Unknown,
    }
}

const fn compare(left: PureValue, right: PureValue, or_equal: bool) -> AbstractBool {
    let (PureValue::U64(left), PureValue::U64(right)) = (left, right) else {
        return AbstractBool::Unknown;
    };
    if (or_equal && left.upper() <= right.lower()) || (!or_equal && left.upper() < right.lower()) {
        AbstractBool::True
    } else if (or_equal && left.lower() > right.upper())
        || (!or_equal && left.lower() >= right.upper())
    {
        AbstractBool::False
    } else {
        AbstractBool::Unknown
    }
}

fn eval_and(values: impl Iterator<Item = AbstractBool>) -> AbstractBool {
    let mut unknown = false;
    for value in values {
        match value {
            AbstractBool::False => return AbstractBool::False,
            AbstractBool::Unknown => unknown = true,
            AbstractBool::True => {}
        }
    }
    if unknown {
        AbstractBool::Unknown
    } else {
        AbstractBool::True
    }
}

fn eval_or(values: impl Iterator<Item = AbstractBool>) -> AbstractBool {
    let mut unknown = false;
    for value in values {
        match value {
            AbstractBool::True => return AbstractBool::True,
            AbstractBool::Unknown => unknown = true,
            AbstractBool::False => {}
        }
    }
    if unknown {
        AbstractBool::Unknown
    } else {
        AbstractBool::False
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::{ByteSpan, VirBlockId, VirContractId, VirFunction, VirFunctionId, VirSignature};

    use super::{SnapshotValues, VcQueryBudget, evaluate_bool};
    use crate::verifier::resource::AbstractBool;
    use crate::verifier::vc::arena::VcTerm;
    use crate::verifier::vc::{VcArena, VcLimits};

    fn function() -> VirFunction {
        VirFunction {
            id: VirFunctionId::new(0),
            name: "vc-test".to_owned(),
            signature: VirSignature {
                parameters: Vec::new(),
                results: Vec::new(),
            },
            contract: VirContractId::new(0),
            entry: VirBlockId::new(0),
            blocks: Vec::new(),
            source_span: ByteSpan::empty(),
        }
    }

    #[test]
    fn normalized_evaluation_preserves_the_existing_operator_results() {
        let limits = VcLimits::default();
        let mut arena = VcArena::default();
        let false_term = arena.intern(VcTerm::Bool(false), limits.max_nodes).unwrap();
        let one = arena.intern(VcTerm::U64(1), limits.max_nodes).unwrap();
        let two = arena.intern(VcTerm::U64(2), limits.max_nodes).unwrap();
        let equal = arena
            .intern(VcTerm::Equal(one, one), limits.max_nodes)
            .unwrap();
        let less = arena
            .intern(VcTerm::LessThan(one, two), limits.max_nodes)
            .unwrap();
        let less_or_equal = arena
            .intern(VcTerm::LessOrEqual(two, two), limits.max_nodes)
            .unwrap();
        let not = arena
            .intern(VcTerm::Not(false_term), limits.max_nodes)
            .unwrap();
        let and = arena
            .intern(
                VcTerm::And(vec![equal, less, less_or_equal, not]),
                limits.max_nodes,
            )
            .unwrap();
        let or = arena
            .intern(VcTerm::Or(vec![false_term, and]), limits.max_nodes)
            .unwrap();
        let mut budget = VcQueryBudget::new(limits);

        assert_eq!(
            evaluate_bool(
                &arena,
                or,
                &BTreeSet::new(),
                SnapshotValues::Results(&[]),
                &function(),
                &mut budget,
            ),
            Some(AbstractBool::True)
        );
    }

    #[test]
    fn trust_and_query_budgets_fail_closed() {
        let limits = VcLimits {
            max_nodes: 1,
            max_normalization_steps: 1,
            max_queries: 1,
            max_query_steps: 1,
        };
        let mut arena = VcArena::default();
        let root = arena.intern(VcTerm::Bool(false), 1).unwrap();
        let trusted = BTreeSet::from([root]);
        let mut budget = VcQueryBudget::new(limits);
        let function = function();

        assert_eq!(
            evaluate_bool(
                &arena,
                root,
                &trusted,
                SnapshotValues::Results(&[]),
                &function,
                &mut budget,
            ),
            Some(AbstractBool::True)
        );
        assert_eq!(
            evaluate_bool(
                &arena,
                root,
                &trusted,
                SnapshotValues::Results(&[]),
                &function,
                &mut budget,
            ),
            None
        );

        let mut no_steps = VcQueryBudget::new(VcLimits {
            max_query_steps: 0,
            ..limits
        });
        assert_eq!(
            evaluate_bool(
                &arena,
                root,
                &BTreeSet::new(),
                SnapshotValues::Results(&[]),
                &function,
                &mut no_steps,
            ),
            None
        );
    }
}
