//! Validation of the runtime-independent HIR specification arenas.

use std::collections::BTreeSet;

use super::super::program::{require, validate_dense};
use super::super::{
    HirIntegerType, HirProgram, HirProgramValidationError, HirSpecBinderOwner, HirSpecClauseOwner,
    HirSpecContractPosition, HirSpecLocation, HirSpecSnapshot, HirSpecTerm, HirSpecTermId,
    HirSpecTermKind, HirTrustPolicyKind, HirTrustScope, HirTypeId, HirTypeKind,
};
use crate::diagnostic::span_contains;

const MAX_SPEC_TERM_DEPTH: usize = 256;

pub(super) fn validate_specs(program: &HirProgram) -> Result<(), HirProgramValidationError> {
    let specs = program.specs();
    validate_dense("spec binder", &specs.binders, |item| item.id.get())?;
    validate_dense("spec term", &specs.terms, |item| item.id.get())?;
    validate_dense("spec clause", &specs.clauses, |item| item.id.get())?;
    validate_dense("spec prove", &specs.proves, |item| item.id.get())?;
    validate_dense("trust entry", &specs.trust_entries, |item| item.id.get())?;
    validate_dense("spec loop invariant", &specs.loop_invariants, |item| {
        item.id.get()
    })?;

    let mut binder_names = BTreeSet::new();
    for binder in &specs.binders {
        let owner_span = match binder.owner {
            HirSpecBinderOwner::Clause(clause_id) => specs
                .clauses
                .get(clause_id.index())
                .filter(|clause| clause.id == clause_id)
                .map(|clause| clause.span),
            HirSpecBinderOwner::Predicate(predicate) => program
                .predicate(predicate)
                .filter(|predicate| predicate.binders.contains(&binder.id))
                .map(|predicate| predicate.span),
        };
        require(
            !binder.name.is_empty()
                && binder_names.insert((binder.owner, binder.name.as_str()))
                && is_spec_scalar_type(program, binder.ty)
                && owner_span.is_some_and(|span| span_contains(span, binder.span)),
            "spec binder",
            binder.id.index(),
            "empty name, invalid type, foreign owner, or span outside owner",
        )?;
    }

    let mut depths = Vec::with_capacity(specs.terms.len());
    for term in &specs.terms {
        let clause = specs
            .clauses
            .get(term.clause.index())
            .filter(|clause| clause.id == term.clause);
        require(
            clause.is_some_and(|clause| span_contains(clause.span, term.span))
                && is_spec_scalar_type(program, term.ty),
            "spec term",
            term.id.index(),
            "missing clause, invalid type, or span outside clause",
        )?;

        let child = |id: HirSpecTermId| {
            specs
                .terms
                .get(id.index())
                .filter(|child| child.id == id && id.index() < term.id.index())
                .filter(|child| child.clause == term.clause)
        };
        let bool_type = |ty| matches!(program.type_kind(ty), Some(HirTypeKind::Bool));
        let u64_type = |ty| {
            matches!(
                program.type_kind(ty),
                Some(HirTypeKind::Integer(HirIntegerType::U64))
            )
        };
        let (valid, depth) = match &term.kind {
            HirSpecTermKind::Bool(_) => (bool_type(term.ty), 1),
            HirSpecTermKind::U64(_) => (u64_type(term.ty), 1),
            HirSpecTermKind::Binder(id) => {
                let binder = specs
                    .binders
                    .get(id.index())
                    .filter(|binder| binder.id == *id);
                (
                    binder.is_some_and(|binder| {
                        binder.ty == term.ty
                            && binder.owner == HirSpecBinderOwner::Clause(term.clause)
                    }),
                    1,
                )
            }
            HirSpecTermKind::Snapshot(snapshot) => {
                (validate_spec_snapshot(program, term, *snapshot), 1)
            }
            HirSpecTermKind::Equal { left, right } => {
                let left_id = *left;
                let right_id = *right;
                let left = child(left_id);
                let right = child(right_id);
                let valid = bool_type(term.ty)
                    && left.zip(right).is_some_and(|(left, right)| {
                        left.ty == right.ty && is_spec_scalar_type(program, left.ty)
                    });
                (valid, child_depth(&depths, left_id, right_id))
            }
            HirSpecTermKind::LessThan { left, right }
            | HirSpecTermKind::LessOrEqual { left, right } => {
                let valid = bool_type(term.ty)
                    && child(*left).is_some_and(|left| u64_type(left.ty))
                    && child(*right).is_some_and(|right| u64_type(right.ty));
                (valid, child_depth(&depths, *left, *right))
            }
            HirSpecTermKind::Not(operand) => {
                let valid = bool_type(term.ty)
                    && child(*operand).is_some_and(|operand| bool_type(operand.ty));
                (valid, unary_depth(&depths, *operand))
            }
            HirSpecTermKind::And(operands) | HirSpecTermKind::Or(operands) => {
                let valid = bool_type(term.ty)
                    && operands.len() >= 2
                    && operands.iter().all(|operand| {
                        child(*operand).is_some_and(|operand| bool_type(operand.ty))
                    });
                (valid, nary_depth(&depths, operands))
            }
        };
        require(
            valid && depth <= MAX_SPEC_TERM_DEPTH,
            "spec term",
            term.id.index(),
            "ill-typed, cyclic/foreign, or exceeds the recursion-depth budget",
        )?;
        depths.push(depth);
    }

    for clause in &specs.clauses {
        let root = specs
            .terms
            .get(clause.root.index())
            .filter(|term| term.id == clause.root && term.clause == clause.id);
        let owner_valid = match clause.owner {
            HirSpecClauseOwner::Contract { contract, position } => program
                .contract(contract)
                .filter(|contract| contract.clauses.contains(&clause.id))
                .is_some_and(|contract| {
                    clause.location
                        == match position {
                            HirSpecContractPosition::Requires => HirSpecLocation::FunctionEntry {
                                function: contract.function,
                            },
                            HirSpecContractPosition::Ensures => HirSpecLocation::FunctionResult {
                                function: contract.function,
                            },
                        }
                }),
            HirSpecClauseOwner::Prove(prove_id) => {
                specs.proves.get(prove_id.index()).is_some_and(|prove| {
                    prove.id == prove_id
                        && prove.clause == clause.id
                        && prove.location == clause.location
                })
            }
            HirSpecClauseOwner::TrustEntry(entry_id) => specs
                .trust_entries
                .get(entry_id.index())
                .is_some_and(|entry| {
                    entry.id == entry_id
                        && entry.clause == clause.id
                        && entry.scope.location() == clause.location
                }),
            HirSpecClauseOwner::LoopInvariant(invariant_id) => specs
                .loop_invariants
                .get(invariant_id.index())
                .is_some_and(|invariant| {
                    invariant.id == invariant_id
                        && invariant.clause == clause.id
                        && invariant.location == clause.location
                }),
        };
        require(
            owner_valid
                && root.is_some_and(|root| {
                    matches!(program.type_kind(root.ty), Some(HirTypeKind::Bool))
                })
                && program
                    .function_by_id(clause.location.function())
                    .is_some_and(|function| span_contains(function.span, clause.span)),
            "spec clause",
            clause.id.index(),
            "invalid owner/location, non-boolean root, or foreign span",
        )?;
    }

    for prove in &specs.proves {
        require(
            program
                .function_by_id(prove.function)
                .is_some_and(|function| {
                    matches!(
                        prove.location,
                        HirSpecLocation::FunctionEntry { function: owner }
                            | HirSpecLocation::FunctionResult { function: owner }
                            if owner == function.id
                    ) && span_contains(function.span, prove.span)
                })
                && specs
                    .clauses
                    .get(prove.clause.index())
                    .is_some_and(|clause| {
                        clause.owner == HirSpecClauseOwner::Prove(prove.id)
                            && clause.location == prove.location
                    }),
            "spec prove",
            prove.id.index(),
            "prove must own a boolean clause at its function entry or result",
        )?;
    }

    for entry in &specs.trust_entries {
        let valid_policy = entry.policy == HirTrustPolicyKind::EntryPointAssumption
            && entry.scope
                == (HirTrustScope::FunctionEntry {
                    function: program.entry_function().id,
                });
        require(
            valid_policy
                && program
                    .function_by_id(entry.scope.function())
                    .is_some_and(|function| span_contains(function.span, entry.span))
                && specs
                    .clauses
                    .get(entry.clause.index())
                    .is_some_and(|clause| {
                        clause.owner == HirSpecClauseOwner::TrustEntry(entry.id)
                            && clause.location == entry.scope.location()
                            && clause.span == entry.span
                    }),
            "trust entry",
            entry.id.index(),
            "policy denied, scope is not the program entry, or clause/origin mismatched",
        )?;
    }

    require(
        specs.loop_invariants.is_empty(),
        "spec loop invariant",
        0,
        "non-trivial loop invariants remain feature gated",
    )
}

fn is_spec_scalar_type(program: &HirProgram, ty: HirTypeId) -> bool {
    matches!(
        program.type_kind(ty),
        Some(HirTypeKind::Bool) | Some(HirTypeKind::Integer(HirIntegerType::U64))
    )
}

fn validate_spec_snapshot(
    program: &HirProgram,
    term: &HirSpecTerm,
    snapshot: HirSpecSnapshot,
) -> bool {
    let Some(clause) = program.specs().clauses.get(term.clause.index()) else {
        return false;
    };
    match snapshot {
        HirSpecSnapshot::Local { function, local } => program
            .function_by_id(function)
            .and_then(|function| function.body.as_ref().map(|body| (function, body)))
            .is_some_and(|(function, body)| {
                clause.location
                    == HirSpecLocation::FunctionEntry {
                        function: function.id,
                    }
                    && body.parameters.contains(&local)
                    && body
                        .locals
                        .get(local.index())
                        .is_some_and(|candidate| candidate.id == local && candidate.ty == term.ty)
            }),
        HirSpecSnapshot::Result { function } => {
            program.function_by_id(function).is_some_and(|function| {
                clause.location
                    == HirSpecLocation::FunctionResult {
                        function: function.id,
                    }
                    && function.signature.return_type == term.ty
            })
        }
    }
}

fn unary_depth(depths: &[usize], operand: HirSpecTermId) -> usize {
    depths
        .get(operand.index())
        .and_then(|depth| depth.checked_add(1))
        .unwrap_or(usize::MAX)
}

fn child_depth(depths: &[usize], left: HirSpecTermId, right: HirSpecTermId) -> usize {
    depths
        .get(left.index())
        .zip(depths.get(right.index()))
        .and_then(|(left, right)| left.max(right).checked_add(1))
        .unwrap_or(usize::MAX)
}

fn nary_depth(depths: &[usize], operands: &[HirSpecTermId]) -> usize {
    operands
        .iter()
        .map(|operand| depths.get(operand.index()).copied())
        .collect::<Option<Vec<_>>>()
        .and_then(|depths| depths.into_iter().max())
        .and_then(|depth| depth.checked_add(1))
        .unwrap_or(usize::MAX)
}
