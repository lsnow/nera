use std::collections::{BTreeMap, BTreeSet};

use crate::{VirFunction, VirSpecSnapshot};

use super::super::resource::{AbstractBool, AbstractValue, PathFact, ResourceState, U64Interval};
use super::arena::{VcArena, VcLimits, VcTerm, VcTermId};
#[cfg(test)]
mod arithmetic_tests;
mod boolean;
mod numeric;
mod opened;
#[cfg(test)]
mod witness_tests;
use crate::verifier::relation::{audit::QueryLog, difference::DifferenceLimits};
use numeric::Number;

#[derive(Clone, Copy)]
pub(in crate::verifier) enum SnapshotValues<'a> {
    State(&'a ResourceState),
    Results(&'a [AbstractValue]),
    Bound {
        state: &'a ResourceState,
        snapshots: &'a BTreeMap<VirSpecSnapshot, (AbstractValue, Option<crate::AffineExpression>)>,
        // Query-local names supplied by the boundary adapter. These do not
        // denote addresses, SSA slots, predicates, or resource permissions.
        booleans: Option<&'a BTreeMap<VirSpecSnapshot, u32>>,
    },
}

impl<'a> SnapshotValues<'a> {
    pub(in crate::verifier) fn state(self) -> Option<&'a ResourceState> {
        match self {
            Self::State(state) | Self::Bound { state, .. } => Some(state),
            Self::Results(_) => None,
        }
    }
}

pub(in crate::verifier) fn evaluate_contract_bool(
    arena: &VcArena,
    root: VcTermId,
    values: SnapshotValues<'_>,
    budget: &mut VcQueryBudget,
) -> Option<AbstractBool> {
    evaluate_value(arena, root, &BTreeSet::new(), values, None, budget).map(bool_value)
}

pub(in crate::verifier) fn evaluate_contract_u64(
    arena: &VcArena,
    root: VcTermId,
    values: SnapshotValues<'_>,
    budget: &mut VcQueryBudget,
) -> Option<u64> {
    match evaluate_value(arena, root, &BTreeSet::new(), values, None, budget)? {
        PureValue::U64(number) => number.interval.exact_value(),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PureValue {
    Unavailable,
    Bool(AbstractBool),
    BooleanIdentity {
        identity: u32,
        negated: bool,
        known: AbstractBool,
    },
    U64(Number),
}

/// Shared budget for every VC query performed while proving one function.
pub(in crate::verifier) struct VcQueryBudget {
    pub(in crate::verifier) exhausted: bool,
    pub(in crate::verifier) relations: QueryLog,
    pub(in crate::verifier) relation_limits: DifferenceLimits,
    remaining_queries: usize,
    remaining_steps: usize,
}

impl VcQueryBudget {
    pub(in crate::verifier) fn new(limits: VcLimits) -> Self {
        Self {
            exhausted: false,
            relations: QueryLog::default(),
            relation_limits: DifferenceLimits::default(),
            remaining_queries: limits.max_queries,
            remaining_steps: limits.max_query_steps,
        }
    }

    pub(in crate::verifier) fn begin_query(&mut self) -> Option<()> {
        self.remaining_queries = self.remaining_queries.checked_sub(1).or_else(|| {
            self.exhausted = true;
            None
        })?;
        Some(())
    }

    pub(in crate::verifier) fn charge(&mut self, amount: usize) -> Option<()> {
        self.remaining_steps = self.remaining_steps.checked_sub(amount).or_else(|| {
            self.exhausted = true;
            None
        })?;
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
    evaluate_value(arena, root, trusted, values, Some(function), budget).map(bool_value)
}

pub(in crate::verifier) fn evaluate_u64(
    arena: &VcArena,
    root: VcTermId,
    values: SnapshotValues<'_>,
    function: &VirFunction,
    budget: &mut VcQueryBudget,
) -> Option<u64> {
    match evaluate_value(
        arena,
        root,
        &BTreeSet::new(),
        values,
        Some(function),
        budget,
    )? {
        PureValue::U64(number) => number.interval.exact_value(),
        _ => None,
    }
}

/// An existential witness must denote an available, well-defined typed value.
/// Symbolic runtime values are allowed, but free binders are not witnesses.
/// The preflight deliberately checks even short-circuited dependencies.
pub(in crate::verifier) fn validate_witness(
    arena: &VcArena,
    root: VcTermId,
    ty: crate::VirSpecType,
    values: SnapshotValues<'_>,
    function: &VirFunction,
    budget: &mut VcQueryBudget,
) -> Option<()> {
    let mut pending = vec![root];
    let mut visited = BTreeSet::new();
    while let Some(id) = pending.pop() {
        budget.charge(1)?;
        if !visited.insert(id) {
            continue;
        }
        let term = arena.get(id)?;
        match term {
            VcTerm::Binder(_) => return None,
            VcTerm::Snapshot(snapshot)
                if matches!(
                    snapshot_value(*snapshot, values, Some(function), budget),
                    PureValue::Unavailable
                ) =>
            {
                return None;
            }
            _ => {}
        }
        budget.charge(term.child_count())?;
        for index in 0..term.child_count() {
            pending.push(term.child_at(index)?);
        }
    }
    match (
        ty,
        evaluate_value(
            arena,
            root,
            &BTreeSet::new(),
            values,
            Some(function),
            budget,
        )?,
    ) {
        (crate::VirSpecType::Bool, PureValue::Bool(_) | PureValue::BooleanIdentity { .. })
        | (crate::VirSpecType::U64, PureValue::U64(_)) => Some(()),
        _ => None,
    }
}

fn evaluate_value(
    arena: &VcArena,
    root: VcTermId,
    trusted: &BTreeSet<VcTermId>,
    values: SnapshotValues<'_>,
    function: Option<&VirFunction>,
    budget: &mut VcQueryBudget,
) -> Option<PureValue> {
    budget.begin_query()?;
    if let Some(state) = values.state()
        && state
            .relations()
            .precision_losses()
            .contains(&crate::verifier::relation::state::RelationPrecisionLoss::Inconsistent)
    {
        return None;
    }
    arena.get(root)?;
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    let mut has_opened = false;
    while let Some(id) = pending.pop() {
        budget.charge(1)?;
        if !seen.insert(id) {
            continue;
        }
        let term = arena.get(id)?;
        if let VcTerm::Snapshot(snapshot @ VirSpecSnapshot::Opened { .. }) = term {
            has_opened = true;
            if matches!(
                snapshot_value(*snapshot, values, function, budget),
                PureValue::Unavailable
            ) {
                return Some(PureValue::Unavailable);
            }
        }
        budget.charge(term.child_count())?;
        for i in 0..term.child_count() {
            pending.push(term.child_at(i)?);
        }
    }
    let mut evaluated = BTreeMap::new();
    let mut stack = vec![(root, 0)];

    while let Some((id, next)) = stack.pop() {
        if evaluated.contains_key(&id) {
            continue;
        }
        if trusted.contains(&id) {
            evaluated.insert(id, PureValue::Bool(AbstractBool::True));
            continue;
        }
        let term = arena.get(id)?;
        if next == 0 {
            budget.charge(1)?;
            // Try the complete opened formula before interval-only children
            // discard relationships between hidden operands. The adapter must
            // prove every new arithmetic intermediate, not just the root.
            if has_opened && let Some(value) = opened::evaluate(arena, id, values, function, budget)
            {
                evaluated.insert(id, value);
                continue;
            }
            if budget.exhausted {
                return None;
            }
        }
        if next > 0 {
            let previous = evaluated.get(&term.child_at(next - 1)?)?;
            let decisive = match (term, previous) {
                (_, PureValue::Unavailable) => Some(PureValue::Unavailable),
                (VcTerm::And(_), value) if bool_value(*value) == AbstractBool::False => {
                    Some(*previous)
                }
                (VcTerm::Or(_), value) if bool_value(*value) == AbstractBool::True => {
                    Some(*previous)
                }
                _ => None,
            };
            if let Some(value) = decisive {
                evaluated.insert(id, value);
                continue;
            }
        }
        if next < term.child_count() {
            budget.charge(1)?;
            let child = term.child_at(next)?;
            arena.get(child)?;
            stack.push((id, next + 1));
            if !evaluated.contains_key(&child) {
                stack.push((child, 0));
            }
            continue;
        }

        evaluated.insert(
            id,
            evaluate_node(term, &evaluated, values, function, budget)?,
        );
    }

    evaluated.get(&root).copied()
}

fn evaluate_node(
    term: &VcTerm,
    evaluated: &BTreeMap<VcTermId, PureValue>,
    values: SnapshotValues<'_>,
    function: Option<&VirFunction>,
    budget: &mut VcQueryBudget,
) -> Option<PureValue> {
    let child = |id: VcTermId| evaluated.get(&id).copied();
    Some(match term {
        VcTerm::Bool(value) => PureValue::Bool(if *value {
            AbstractBool::True
        } else {
            AbstractBool::False
        }),
        VcTerm::U64(value) => PureValue::U64(Number::exact(*value)),
        VcTerm::CheckedAdd(left, right) | VcTerm::CheckedSub(left, right) => {
            let (PureValue::U64(left), PureValue::U64(right)) = (child(*left)?, child(*right)?)
            else {
                return Some(PureValue::Unavailable);
            };
            numeric::arithmetic(
                left,
                right,
                matches!(term, VcTerm::CheckedSub(..)),
                values,
                budget,
            )?
            .map_or(PureValue::Unavailable, PureValue::U64)
        }
        VcTerm::CheckedScale(operand, stride) => {
            let PureValue::U64(value) = child(*operand)? else {
                return Some(PureValue::Unavailable);
            };
            numeric::scale(value, *stride).map_or(PureValue::Unavailable, PureValue::U64)
        }
        VcTerm::RangeContains(ends) | VcTerm::RangeDisjoint(ends) => {
            let mut numbers = [Number::exact(0); 4];
            for (out, id) in numbers.iter_mut().zip(ends) {
                let PureValue::U64(value) = child(*id)? else {
                    return Some(PureValue::Unavailable);
                };
                *out = value;
            }
            PureValue::Bool(numeric::range(
                numbers,
                matches!(term, VcTerm::RangeDisjoint(_)),
                values,
                budget,
            )?)
        }
        VcTerm::Binder(_) => PureValue::Bool(AbstractBool::Unknown),
        VcTerm::Snapshot(snapshot) => snapshot_value(*snapshot, values, function, budget),
        VcTerm::Equal(left, right) => {
            if left == right {
                PureValue::Bool(AbstractBool::True)
            } else {
                PureValue::Bool(match (child(*left)?, child(*right)?) {
                    (PureValue::U64(a), PureValue::U64(b)) => numeric::equal(a, b, values, budget)?,
                    (a, b) => equal(a, b),
                })
            }
        }
        VcTerm::LessThan(left, right) | VcTerm::LessOrEqual(left, right)
            if left == right && matches!(child(*left)?, PureValue::U64(_)) =>
        {
            PureValue::Bool(if matches!(term, VcTerm::LessOrEqual(..)) {
                AbstractBool::True
            } else {
                AbstractBool::False
            })
        }
        VcTerm::LessThan(left, right) => PureValue::Bool(compare(
            child(*left)?,
            child(*right)?,
            false,
            values,
            budget,
        )?),
        VcTerm::LessOrEqual(left, right) => PureValue::Bool(compare(
            child(*left)?,
            child(*right)?,
            true,
            values,
            budget,
        )?),
        VcTerm::Not(operand) => boolean::not(child(*operand)?),
        VcTerm::And(operands) => boolean::junction(
            operands
                .iter()
                .map(|operand| child(*operand))
                .collect::<Option<Vec<_>>>()?,
            false,
        ),
        VcTerm::Or(operands) => boolean::junction(
            operands
                .iter()
                .map(|operand| child(*operand))
                .collect::<Option<Vec<_>>>()?,
            true,
        ),
    })
}

fn snapshot_value(
    snapshot: VirSpecSnapshot,
    values: SnapshotValues<'_>,
    function: Option<&VirFunction>,
    budget: &mut VcQueryBudget,
) -> PureValue {
    if let VirSpecSnapshot::Opened {
        function: owner,
        action,
        holder,
        binder,
    } = snapshot
    {
        if budget
            .charge(crate::predicate_logic::MAX_SUBSTITUTION_NODES)
            .is_none()
        {
            return PureValue::Unavailable;
        }
        if function.is_none_or(|f| f.id != owner) {
            return PureValue::Unavailable;
        }
        return match values
            .state()
            .and_then(|state| state.opened_predicate_snapshot(action, holder, binder))
        {
            Some((AbstractValue::U64(interval), expression)) => {
                PureValue::U64(Number::new(interval, expression))
            }
            Some((AbstractValue::Bool(value), _)) => PureValue::Bool(value),
            _ => PureValue::Unavailable,
        };
    }
    if let SnapshotValues::Bound {
        snapshots,
        booleans,
        ..
    } = values
    {
        return match snapshots.get(&snapshot) {
            Some((AbstractValue::U64(interval), expression)) => {
                PureValue::U64(Number::new(*interval, *expression))
            }
            Some((AbstractValue::Bool(value), _)) => booleans
                .and_then(|ids| ids.get(&snapshot))
                .map_or(PureValue::Bool(*value), |identity| {
                    PureValue::BooleanIdentity {
                        identity: *identity,
                        negated: false,
                        known: *value,
                    }
                }),
            _ => PureValue::Unavailable,
        };
    }
    let Some(function) = function else {
        return PureValue::Unavailable;
    };
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
        Some(AbstractValue::U64(value)) => {
            let expression = match (snapshot, values) {
                (VirSpecSnapshot::Value { value, .. }, SnapshotValues::State(state)) => Some(
                    state
                        .word_expression(value)
                        .unwrap_or_else(|| crate::AffineExpression::identity(value)),
                ),
                (VirSpecSnapshot::Parameter { slot, .. }, SnapshotValues::State(state)) => function
                    .blocks
                    .iter()
                    .find(|b| b.id == function.entry)
                    .and_then(|b| b.parameters.get(slot as usize))
                    .map(|p| {
                        state
                            .word_expression(p.id)
                            .unwrap_or_else(|| crate::AffineExpression::identity(p.id))
                    }),
                _ => None,
            };
            PureValue::U64(Number::new(value, expression))
        }
        _ => PureValue::Unavailable,
    }
}

const fn bool_value(value: PureValue) -> AbstractBool {
    match value {
        PureValue::Bool(value) | PureValue::BooleanIdentity { known: value, .. } => value,
        PureValue::U64(_) | PureValue::Unavailable => AbstractBool::Unknown,
    }
}

fn equal(left: PureValue, right: PureValue) -> AbstractBool {
    if let (
        PureValue::BooleanIdentity {
            identity: a,
            negated: an,
            ..
        },
        PureValue::BooleanIdentity {
            identity: b,
            negated: bn,
            ..
        },
    ) = (left, right)
        && a == b
    {
        return if an == bn {
            AbstractBool::True
        } else {
            AbstractBool::False
        };
    }
    match (left, right) {
        (
            PureValue::Bool(_) | PureValue::BooleanIdentity { .. },
            PureValue::Bool(_) | PureValue::BooleanIdentity { .. },
        ) => match (bool_value(left), bool_value(right)) {
            (AbstractBool::True, AbstractBool::True)
            | (AbstractBool::False, AbstractBool::False) => AbstractBool::True,
            (AbstractBool::True, AbstractBool::False)
            | (AbstractBool::False, AbstractBool::True) => AbstractBool::False,
            _ => AbstractBool::Unknown,
        },
        _ => AbstractBool::Unknown,
    }
}

fn compare(
    left: PureValue,
    right: PureValue,
    or_equal: bool,
    values: SnapshotValues<'_>,
    budget: &mut VcQueryBudget,
) -> Option<AbstractBool> {
    let (PureValue::U64(left), PureValue::U64(right)) = (left, right) else {
        return Some(AbstractBool::Unknown);
    };
    if or_equal {
        numeric::le(left, right, values, budget)
    } else {
        Some(numeric::not(numeric::le(right, left, values, budget)?))
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

    pub(super) fn function() -> VirFunction {
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
    fn unavailable_opened_names_cannot_hide_behind_short_circuit_or_reflexivity() {
        let limits = VcLimits::default();
        let mut arena = VcArena::default();
        let function = function();
        let opened = arena
            .intern(
                VcTerm::Snapshot(crate::VirSpecSnapshot::Opened {
                    function: function.id,
                    action: 7,
                    holder: 3,
                    binder: 0,
                }),
                limits.max_nodes,
            )
            .unwrap();
        let same = arena
            .intern(VcTerm::Equal(opened, opened), limits.max_nodes)
            .unwrap();
        let yes = arena.intern(VcTerm::Bool(true), limits.max_nodes).unwrap();
        let hidden = arena
            .intern(VcTerm::Or(vec![yes, same]), limits.max_nodes)
            .unwrap();
        let state = crate::ResourceState::new();
        for root in [same, hidden] {
            let mut budget = VcQueryBudget::new(limits);
            assert_eq!(
                evaluate_bool(
                    &arena,
                    root,
                    &BTreeSet::new(),
                    SnapshotValues::State(&state),
                    &function,
                    &mut budget
                ),
                Some(AbstractBool::Unknown)
            );
        }
    }

    #[test]
    fn opened_observation_work_is_charged_to_the_vc_budget() {
        let limits = VcLimits {
            max_query_steps: 8,
            ..VcLimits::default()
        };
        let mut arena = VcArena::default();
        let function = function();
        let root = arena
            .intern(
                VcTerm::Snapshot(crate::VirSpecSnapshot::Opened {
                    function: function.id,
                    action: 0,
                    holder: 0,
                    binder: 0,
                }),
                limits.max_nodes,
            )
            .unwrap();
        let mut budget = VcQueryBudget::new(limits);
        assert_ne!(
            evaluate_bool(
                &arena,
                root,
                &BTreeSet::new(),
                SnapshotValues::State(&crate::ResourceState::new()),
                &function,
                &mut budget
            ),
            Some(AbstractBool::True)
        );
        assert!(budget.exhausted);
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
