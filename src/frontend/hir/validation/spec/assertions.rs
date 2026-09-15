//! Structural resource assertions and lexical existential scope, not proofs.
use super::*;
use crate::spec_assertion::{ScopeNode, extend, valid_scopes};
use crate::{HirSpecRoot, SpecAssertionKind, SpecMemoryClaim};

pub(super) fn validate(program: &HirProgram) -> Result<(), HirProgramValidationError> {
    let specs = program.specs();
    if specs.assertions.is_empty() {
        return Ok(());
    }
    let mut nodes = Vec::new();
    for (index, assertion) in specs.assertions.iter().enumerate() {
        let clause = specs.clauses.get(assertion.clause.index());
        require(
            assertion.id.index() == index
                && clause.is_some_and(|clause| {
                    matches!(
                        clause.owner,
                        HirSpecClauseOwner::Prove(_)
                            | HirSpecClauseOwner::Contract { .. }
                            | HirSpecClauseOwner::LoopInvariant(_)
                    ) && span_contains(clause.span, assertion.span)
                }),
            "spec assertion",
            index,
            "invalid identity, owner or origin",
        )?;
        let term = |id: crate::HirSpecTermId| {
            specs
                .terms
                .get(id.index())
                .filter(|t| t.id == id && t.clause == assertion.clause)
        };
        let scalar = |id, bool_ty| {
            term(id).is_some_and(|t| {
                matches!(
                    (program.type_kind(t.ty), bool_ty),
                    (Some(HirTypeKind::Bool), true)
                        | (
                            Some(HirTypeKind::Integer(
                                HirIntegerType::U64 | HirIntegerType::Usize
                            )),
                            false
                        )
                )
            })
        };
        let child = |id: crate::HirSpecAssertionId| {
            id.index() < index
                && specs
                    .assertions
                    .get(id.index())
                    .is_some_and(|a| a.id == id && a.clause == assertion.clause)
        };
        let mut node = ScopeNode {
            terms: vec![],
            children: vec![],
            binder: None,
        };
        let valid = match &assertion.kind {
            SpecAssertionKind::Footprint { range, .. } => {
                let owner = clause.is_some_and(|c| {
                    matches!(
                        c.owner,
                        HirSpecClauseOwner::Contract {
                            position: HirSpecContractPosition::Requires,
                            ..
                        }
                    ) && c.root == HirSpecRoot::Assertion(assertion.id)
                });
                owner
                    && range.as_ref().is_none_or(|r| {
                        node.terms
                            .extend([r.start_bytes.index(), r.end_bytes.index()]);
                        scalar(r.start_bytes, false)
                            && scalar(r.end_bytes, false)
                            && is_spec_scalar_type(program, r.layout)
                            && valid_pointer(
                                program,
                                assertion.clause,
                                r.pointer,
                                Some(r.layout),
                                false,
                            )
                    })
            }
            SpecAssertionKind::Disjoint { left, right } => {
                node.terms.extend([
                    left.start_bytes.index(),
                    left.end_bytes.index(),
                    right.start_bytes.index(),
                    right.end_bytes.index(),
                ]);
                [left, right].iter().all(|range| {
                    scalar(range.start_bytes, false)
                        && scalar(range.end_bytes, false)
                        && is_spec_scalar_type(program, range.layout)
                        && valid_pointer(
                            program,
                            assertion.clause,
                            range.pointer,
                            Some(range.layout),
                            false,
                        )
                })
            }
            SpecAssertionKind::Alive(pointer) => {
                valid_pointer(program, assertion.clause, *pointer, None, false)
            }
            SpecAssertionKind::SameAllocation { left, right } => {
                valid_pointer(program, assertion.clause, *left, None, false)
                    && valid_pointer(program, assertion.clause, *right, None, false)
            }
            SpecAssertionKind::Initialized {
                pointer,
                start_bytes,
                end_bytes,
                layout,
            } => {
                node.terms.extend([start_bytes.index(), end_bytes.index()]);
                scalar(*start_bytes, false)
                    && scalar(*end_bytes, false)
                    && valid_pointer(program, assertion.clause, *pointer, Some(*layout), false)
            }
            SpecAssertionKind::Pure(id) => {
                node.terms.push(id.index());
                scalar(*id, true)
            }
            SpecAssertionKind::Permission(memory) | SpecAssertionKind::PointsTo { memory, .. } => {
                node.terms
                    .extend([memory.start_bytes.index(), memory.end_bytes.index()]);
                let mut valid = scalar(memory.start_bytes, false)
                    && scalar(memory.end_bytes, false)
                    && valid_memory(program, assertion.clause, memory);
                if let SpecAssertionKind::PointsTo {
                    value: Some(value), ..
                } = &assertion.kind
                {
                    node.terms.push(value.index());
                    valid &= term(*value).is_some_and(|t| t.ty == memory.layout);
                }
                valid
            }
            SpecAssertionKind::Separation(children) => {
                node.children.extend(children.iter().map(|id| id.index()));
                children.len() >= 2 && children.iter().all(|id| child(*id))
            }
            SpecAssertionKind::Exists {
                binder,
                body,
                witness,
            } => {
                node.children.push(body.index());
                node.binder = Some(binder.get());
                node.terms.extend(witness.iter().map(|id| id.index()));
                child(*body)
                    && specs.binders.get(binder.index()).is_some_and(|b| {
                        b.id == *binder
                            && b.owner == HirSpecBinderOwner::Clause(assertion.clause)
                            && witness.is_none_or(|id| term(id).is_some_and(|t| t.ty == b.ty))
                    })
            }
        };
        require(
            valid,
            "spec assertion",
            index,
            "ill-typed, foreign, forward reference or invalid memory snapshot",
        )?;
        nodes.push(node);
    }
    let mut free: Vec<BTreeSet<u32>> = Vec::new();
    let mut budget = 1_000_000;
    for term in &specs.terms {
        let mut vars = BTreeSet::new();
        let children = match &term.kind {
            HirSpecTermKind::Binder(id) => {
                vars.insert(id.get());
                vec![]
            }
            HirSpecTermKind::CheckedAdd { left, right }
            | HirSpecTermKind::CheckedSub { left, right }
            | HirSpecTermKind::Equal { left, right }
            | HirSpecTermKind::LessThan { left, right }
            | HirSpecTermKind::LessOrEqual { left, right } => vec![*left, *right],
            HirSpecTermKind::Not(id) | HirSpecTermKind::CheckedScale { operand: id, .. } => {
                vec![*id]
            }
            HirSpecTermKind::RangeContains {
                outer_start: a,
                outer_end: b,
                inner_start: c,
                inner_end: d,
            }
            | HirSpecTermKind::RangeDisjoint {
                left_start: a,
                left_end: b,
                right_start: c,
                right_end: d,
            } => vec![*a, *b, *c, *d],
            HirSpecTermKind::And(ids) | HirSpecTermKind::Or(ids) => ids.clone(),
            _ => vec![],
        };
        for id in children {
            require(
                extend(&mut vars, &free[id.index()], &mut budget),
                "spec assertion",
                0,
                "scope work budget exceeded",
            )?;
        }
        free.push(vars);
    }
    let roots: Vec<_> = specs
        .clauses
        .iter()
        .map(|c| match c.root {
            HirSpecRoot::Pure(id) => ScopeNode {
                terms: vec![id.index()],
                children: vec![],
                binder: None,
            },
            HirSpecRoot::Assertion(id) => ScopeNode {
                terms: vec![],
                children: vec![id.index()],
                binder: None,
            },
        })
        .collect();
    require(
        valid_scopes(&free, &nodes, &roots),
        "spec assertion",
        0,
        "existential escapes, duplicate binder, or graph budget exceeded",
    )
}

fn valid_memory(
    program: &HirProgram,
    clause: crate::HirSpecClauseId,
    memory: &SpecMemoryClaim<HirSpecSnapshot, crate::HirSpecTermId, HirTypeId>,
) -> bool {
    // First profile: sized scalar pointees. No ghost-only layout reaches runtime.
    if !is_spec_scalar_type(program, memory.layout) {
        return false;
    }
    valid_pointer(program, clause, memory.pointer, Some(memory.layout), false)
        && valid_pointer(program, clause, memory.authority, Some(memory.layout), true)
}

fn valid_pointer(
    program: &HirProgram,
    clause: crate::HirSpecClauseId,
    snapshot: HirSpecSnapshot,
    layout: Option<HirTypeId>,
    authority: bool,
) -> bool {
    let ty = match snapshot {
        HirSpecSnapshot::EntryParameter { .. }
        | HirSpecSnapshot::LoopEntry { .. }
        | HirSpecSnapshot::Memory { .. }
        | HirSpecSnapshot::Length { .. } => return false,
        HirSpecSnapshot::Local { function, local } => program
            .function_by_id(function)
            .and_then(|f| f.body())
            .and_then(|b| b.locals.get(local.index()))
            .map(|l| l.ty),
        HirSpecSnapshot::Result { function } => program
            .function_by_id(function)
            .map(|f| f.signature.return_type),
    };
    let Some(ty) = ty else {
        return false;
    };
    if authority && matches!(program.type_kind(ty), Some(HirTypeKind::RawPointer { .. })) {
        return false;
    }
    let pointee = match program.type_kind(ty) {
        Some(
            HirTypeKind::RawPointer { pointee, .. }
            | HirTypeKind::Reference { pointee, .. }
            | HirTypeKind::Own { pointee },
        ) => *pointee,
        Some(HirTypeKind::Slice { element, .. }) => *element,
        _ => return false,
    };
    let pointee = match program.type_kind(pointee) {
        Some(HirTypeKind::Slice { element, .. }) => *element,
        Some(HirTypeKind::Array { element, .. })
            if matches!(
                program.specs().clauses[clause.index()].owner,
                HirSpecClauseOwner::LoopInvariant(_)
            ) =>
        {
            *element
        }
        _ => pointee,
    };
    layout.is_none_or(|layout| pointee == layout)
        && validate_spec_snapshot(
            program,
            &HirSpecTerm {
                id: HirSpecTermId::new(0),
                clause,
                ty,
                kind: HirSpecTermKind::Snapshot(snapshot),
                span: program.specs().clauses[clause.index()].span,
            },
            snapshot,
        )
}
