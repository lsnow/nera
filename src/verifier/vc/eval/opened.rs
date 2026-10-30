//! Convert bounded VC scalar formulas to predicate queries. Snapshot ownership is
//! checked here; opening actions and actual sources belong to the resource
//! adapter, and arithmetic/entailment remain in the pure expression service.
use super::*;
use crate::verifier::resource::{
    OpenedSpecComparison as Comparison, OpenedSpecOperand as Operand, OpenedSpecTerm as Term,
};

struct Query {
    terms: Vec<Term>,
    mapped: BTreeMap<VcTermId, u32>,
    has_opened: bool,
}

impl Query {
    fn operand(
        &mut self,
        arena: &VcArena,
        id: VcTermId,
        function: &VirFunction,
        depth: usize,
        budget: &mut VcQueryBudget,
    ) -> Option<u32> {
        budget.charge(1)?;
        if depth > crate::predicate_logic::MAX_EXPRESSION_DEPTH {
            budget.exhausted = true;
            return None;
        }
        if let Some(id) = self.mapped.get(&id) {
            return Some(*id);
        }
        let term = match arena.get(id)? {
            VcTerm::Snapshot(VirSpecSnapshot::Opened {
                function: owner,
                action,
                holder,
                binder,
            }) if *owner == function.id => {
                self.has_opened = true;
                Term::Operand(Operand::Opened {
                    action: *action,
                    holder: *holder,
                    binder: *binder,
                })
            }
            VcTerm::Snapshot(VirSpecSnapshot::Value {
                function: owner,
                value,
            }) if *owner == function.id => Term::Operand(Operand::Value(*value)),
            VcTerm::U64(n) => Term::Operand(Operand::Word(*n)),
            VcTerm::Bool(b) => Term::Operand(Operand::Bool(*b)),
            VcTerm::CheckedAdd(a, b) | VcTerm::CheckedSub(a, b) => {
                let a = self.operand(arena, *a, function, depth + 1, budget)?;
                let b = self.operand(arena, *b, function, depth + 1, budget)?;
                if matches!(arena.get(id)?, VcTerm::CheckedAdd(..)) {
                    Term::Add(a, b)
                } else {
                    Term::Sub(a, b)
                }
            }
            VcTerm::CheckedScale(a, factor) => Term::Scale(
                self.operand(arena, *a, function, depth + 1, budget)?,
                *factor,
            ),
            VcTerm::Equal(a, b) | VcTerm::LessThan(a, b) | VcTerm::LessOrEqual(a, b) => {
                let left = self.operand(arena, *a, function, depth + 1, budget)?;
                let right = self.operand(arena, *b, function, depth + 1, budget)?;
                match arena.get(id)? {
                    VcTerm::Equal(..) => Term::Equal(left, right),
                    VcTerm::LessThan(..) => Term::Less(left, right),
                    _ => Term::LessEqual(left, right),
                }
            }
            VcTerm::Not(a) => Term::Not(self.operand(arena, *a, function, depth + 1, budget)?),
            VcTerm::And(children) | VcTerm::Or(children) => {
                let and = matches!(arena.get(id)?, VcTerm::And(_));
                let mut children = children.iter();
                let Some(first) = children.next() else {
                    return self.push(id, Term::Operand(Operand::Bool(and)), budget);
                };
                let mut result = self.operand(arena, *first, function, depth + 1, budget)?;
                for child in children {
                    let child = self.operand(arena, *child, function, depth + 1, budget)?;
                    let term = if and {
                        Term::And(result, child)
                    } else {
                        Term::Or(result, child)
                    };
                    result = self.push(id, term, budget)?;
                }
                self.mapped.insert(id, result);
                return Some(result);
            }
            _ => return None,
        };
        self.push(id, term, budget)
    }

    fn push(&mut self, id: VcTermId, term: Term, budget: &mut VcQueryBudget) -> Option<u32> {
        budget.charge(1)?;
        if self.terms.len() >= crate::predicate_logic::MAX_EXPRESSION_NODES {
            budget.exhausted = true;
            return None;
        }
        let result = self.terms.len() as u32;
        self.terms.push(term);
        self.mapped.insert(id, result);
        Some(result)
    }
}

pub(super) fn evaluate(
    arena: &VcArena,
    root: VcTermId,
    values: SnapshotValues<'_>,
    function: Option<&VirFunction>,
    budget: &mut VcQueryBudget,
) -> Option<PureValue> {
    if !matches!(
        arena.get(root)?,
        VcTerm::Equal(..)
            | VcTerm::LessThan(..)
            | VcTerm::LessOrEqual(..)
            | VcTerm::Not(_)
            | VcTerm::And(_)
            | VcTerm::Or(_)
    ) {
        return None;
    }
    let state = values.state()?;
    let function = function?;
    // An unrelated ordinary comparison must not acquire the predicate DAG's
    // smaller node/depth limits merely because this adapter was consulted.
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    let mut has_opened = false;
    while let Some(id) = pending.pop() {
        budget.charge(1)?;
        if !seen.insert(id) {
            continue;
        }
        let term = arena.get(id)?;
        if matches!(term, VcTerm::Snapshot(VirSpecSnapshot::Opened { .. })) {
            has_opened = true;
            break;
        }
        for index in 0..term.child_count() {
            pending.push(term.child_at(index)?);
        }
    }
    if !has_opened {
        return None;
    }
    let mut query = Query {
        terms: vec![],
        mapped: BTreeMap::new(),
        has_opened: false,
    };
    let root = query.operand(arena, root, function, 1, budget)?;
    if !query.has_opened {
        return None;
    }
    budget.charge(crate::predicate_logic::MAX_SUBSTITUTION_NODES)?;
    let comparison = match query.terms[root as usize] {
        Term::Equal(a, b) => Some((Comparison::Equal, a, b)),
        Term::Less(a, b) => Some((Comparison::Less, a, b)),
        Term::LessEqual(a, b) => Some((Comparison::LessEqual, a, b)),
        _ => None,
    };
    let result = if let Some((comparison, left, right)) = comparison {
        match (query.terms[left as usize], query.terms[right as usize]) {
            (Term::Operand(left), Term::Operand(right)) => {
                state.prove_opened_spec_comparison(comparison, left, right)
            }
            _ => state.prove_opened_spec_formula(&query.terms, root),
        }
    } else {
        state.prove_opened_spec_formula(&query.terms, root)
    };
    match result {
        Ok(true) => Some(PureValue::Bool(AbstractBool::True)),
        Ok(false) => None,
        Err(crate::verifier::resource::PredicateError::Budget) => {
            budget.exhausted = true;
            None
        }
        Err(_) => Some(PureValue::Unavailable),
    }
}

#[cfg(test)]
mod tests;
