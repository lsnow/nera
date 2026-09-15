//! Scalar atoms and admission for structured stable-resource induction.
use super::*;
use crate::{
    VirSpecEnvironment, VirSpecSnapshot as S, VirSpecTermId, VirSpecTermKind as T, VirSpecType,
};

#[derive(Clone, Copy)]
pub(crate) enum ScalarOperand {
    Value(VirValueId),
    Constant(u64),
}

#[derive(Clone, Copy)]
pub(crate) enum ScalarLoopAtom {
    Constant,
    Boolean(VirValueId, bool),
    Compare {
        left: ScalarOperand,
        right: ScalarOperand,
        strict: bool,
        equal: bool,
    },
}

pub(crate) fn scalar_atoms(
    specs: &VirSpecEnvironment,
    root: VirSpecTermId,
) -> Option<Vec<ScalarLoopAtom>> {
    let term = |id: VirSpecTermId| specs.terms().get(id.get() as usize);
    let operand = |id| match term(id)?.kind {
        T::U64(n) => Some(ScalarOperand::Constant(n)),
        T::Snapshot(S::Value { value, .. }) if term(id)?.ty == VirSpecType::U64 => {
            Some(ScalarOperand::Value(value))
        }
        _ => None,
    };
    let boolean = |id| match term(id)?.kind {
        T::Snapshot(S::Value { value, .. }) if term(id)?.ty == VirSpecType::Bool => Some(value),
        _ => None,
    };
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    let mut result = Vec::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        result.push(match &term(id)?.kind {
            T::Bool(_) => ScalarLoopAtom::Constant,
            T::And(children) => {
                pending.extend(children);
                continue;
            }
            T::Snapshot(_) => ScalarLoopAtom::Boolean(boolean(id)?, true),
            T::Not(child) => ScalarLoopAtom::Boolean(boolean(*child)?, false),
            kind @ (T::Equal { left, right }
            | T::LessThan { left, right }
            | T::LessOrEqual { left, right }) => ScalarLoopAtom::Compare {
                left: operand(*left)?,
                right: operand(*right)?,
                strict: matches!(kind, T::LessThan { .. }),
                equal: matches!(kind, T::Equal { .. }),
            },
            _ => return None,
        });
    }
    Some(result)
}

impl VirLoopBoundary {
    /// Reject fresh storage/non-monotone effects and unaccounted cycles.
    /// Scalar accesses and loan effects are independently checked by VIR.
    pub(crate) fn induction_profile(
        &self,
        function: &VirFunction,
        specs: &VirSpecEnvironment,
        functions: &[VirFunction],
    ) -> bool {
        if function.blocks.iter().any(|b| {
            b.instructions.iter().any(|i| {
                self.blocks.contains(&b.id)
                    && !super::resources::stable_resource_instruction(&i.instruction)
            })
        }) {
            return false;
        }
        if !super::resources::stable_calls(function, self, functions) {
            return false;
        }
        for i in specs
            .loop_invariants()
            .iter()
            .filter(|i| i.function == function.id)
        {
            let Some(boundary) = i.boundary.as_ref() else {
                return false;
            };
            let admitted = match specs.clause(i.clause).map(|c| &c.kind) {
                Some(crate::VirSpecClauseKind::Logic { root }) => {
                    scalar_atoms(specs, *root).is_some()
                }
                Some(crate::VirSpecClauseKind::Assertion { root }) => {
                    super::resource_atom(specs, *root).is_some()
                        || super::conditional_resource_atom(specs, *root).is_some()
                }
                _ => false,
            };
            if !admitted || specs.terms().iter().filter(|t| t.clause == i.clause).any(|t|
                matches!(t.kind, T::Snapshot(S::Value { value, .. }) if !boundary.bindings.iter().any(|b| b.head == value)))
            { return false; }
        }
        // Cutting validated back edges inside this region must yield a DAG.
        // Unrelated cycles remain the ordinary CFG analyzer's responsibility;
        // an unannotated child cannot hide inside an inductive outer loop.
        let mut remaining: BTreeSet<_> = self.blocks.iter().copied().collect();
        while !remaining.is_empty() {
            let ready: Vec<_> = remaining
                .iter()
                .copied()
                .filter(|id| {
                    !function.blocks.iter().any(|b| {
                        remaining.contains(&b.id)
                            && targets(&b.terminator.terminator).iter().any(|(_, t)| {
                                t.is_some_and(|t| {
                                    t.block == *id
                                        && !specs
                                            .loop_invariants()
                                            .iter()
                                            .filter(|i| i.function == function.id)
                                            .any(|i| {
                                                i.boundary.as_ref().is_some_and(|boundary| {
                                                    members_back(boundary, b.id, t.block)
                                                })
                                            })
                                })
                            })
                    })
                })
                .collect();
            if ready.is_empty() {
                return false;
            }
            for id in ready {
                remaining.remove(&id);
            }
        }
        true
    }
}

/// A bounded pure guard, not a conjunction to install as a havoc premise.
pub(super) fn scalar_predicate(specs: &VirSpecEnvironment, root: VirSpecTermId) -> bool {
    let mut pending = vec![root];
    let mut seen = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        if seen.len() > 64 {
            return false;
        }
        let Some(term) = specs.terms().get(id.get() as usize) else {
            return false;
        };
        match &term.kind {
            T::U64(_) | T::Bool(_) | T::Snapshot(S::Value { .. }) => {}
            T::Not(child) => pending.push(*child),
            T::And(children) | T::Or(children) => pending.extend(children),
            T::Equal { left, right }
            | T::LessThan { left, right }
            | T::LessOrEqual { left, right } => pending.extend([left, right]),
            _ => return false,
        }
    }
    true
}

fn members_back(boundary: &VirLoopBoundary, source: VirBlockId, target: VirBlockId) -> bool {
    target == boundary.header && boundary.blocks.contains(&source)
}
