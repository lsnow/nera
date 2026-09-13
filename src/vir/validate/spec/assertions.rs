//! Resource syntax validation uses existing runtime snapshots and memory schema.
use super::*;
use crate::spec_assertion::{ScopeNode, extend, valid_scopes};
use crate::{SpecAssertionKind as A, VirSpecTermKind as T, VirSpecType};

pub(super) fn validate(unit: &VirUnit) -> Result<(), VirValidationError> {
    let specs = &unit.specs;
    if specs.assertions().is_empty() {
        return Ok(());
    }
    let mut nodes = Vec::new();
    for (index, assertion) in specs.assertions().iter().enumerate() {
        let bad = || program_error(VirValidationErrorKind::InvalidSpecAssertion(assertion.id));
        let clause = specs.clause(assertion.clause).ok_or_else(bad)?;
        if assertion.id.get() as usize != index
            || !matches!(clause.owner, crate::VirSpecClauseOwner::Prove(_))
            || !origins_are_nested(unit, clause.origin.origin(), assertion.origin)
        {
            return Err(bad());
        }
        let term = |id: crate::VirSpecTermId| {
            specs
                .terms()
                .get(id.get() as usize)
                .filter(|t| t.id == id && t.clause == assertion.clause)
        };
        let scalar = |id, ty| term(id).is_some_and(|t| t.ty == ty);
        let child = |id: crate::VirSpecAssertionId| {
            (id.get() as usize) < index
                && specs
                    .assertions()
                    .get(id.get() as usize)
                    .is_some_and(|a| a.id == id && a.clause == assertion.clause)
        };
        let mut node = ScopeNode {
            terms: vec![],
            children: vec![],
            binder: None,
        };
        let valid = match &assertion.kind {
            A::Alive(pointer) => valid_pointer(unit, clause, *pointer, None),
            A::SameAllocation { left, right } => {
                valid_pointer(unit, clause, *left, None)
                    && valid_pointer(unit, clause, *right, None)
            }
            A::Initialized {
                pointer,
                start_bytes,
                end_bytes,
                layout,
            } => {
                node.terms
                    .extend([start_bytes.get() as usize, end_bytes.get() as usize]);
                scalar(*start_bytes, VirSpecType::U64)
                    && scalar(*end_bytes, VirSpecType::U64)
                    && unit.memory.resolves_access(*layout)
                    && valid_pointer(unit, clause, *pointer, Some(*layout))
            }
            A::Pure(id) => {
                node.terms.push(id.get() as usize);
                scalar(*id, VirSpecType::Bool)
            }
            A::Permission(memory) | A::PointsTo { memory, .. } => {
                node.terms.extend([
                    memory.start_bytes.get() as usize,
                    memory.end_bytes.get() as usize,
                ]);
                let layout_ty = match unit.memory.kind(memory.layout.ty) {
                    Some(crate::VirMemoryTypeKind::Bool) => Some(VirSpecType::Bool),
                    Some(crate::VirMemoryTypeKind::Integer(crate::VirIntegerType::U64)) => {
                        Some(VirSpecType::U64)
                    }
                    _ => None,
                };
                let mut valid = scalar(memory.start_bytes, VirSpecType::U64)
                    && scalar(memory.end_bytes, VirSpecType::U64)
                    && unit.memory.resolves_access(memory.layout)
                    && layout_ty.is_some()
                    && valid_pointer(unit, clause, memory.pointer, Some(memory.layout))
                    && validate_snapshot_type(unit, clause, memory.authority, |ty| {
                        ty == VirType::Permission
                    });
                if let A::PointsTo {
                    value: Some(value), ..
                } = &assertion.kind
                {
                    node.terms.push(value.get() as usize);
                    valid &= term(*value).is_some_and(|t| Some(t.ty) == layout_ty);
                }
                valid
            }
            A::Separation(children) => {
                node.children
                    .extend(children.iter().map(|id| id.get() as usize));
                children.len() >= 2 && children.iter().all(|id| child(*id))
            }
            A::Exists {
                binder,
                body,
                witness,
            } => {
                node.children.push(body.get() as usize);
                node.binder = Some(binder.get());
                node.terms
                    .extend(witness.iter().map(|id| id.get() as usize));
                child(*body)
                    && specs.binders().get(binder.get() as usize).is_some_and(|b| {
                        b.id == *binder
                            && b.owner == crate::VirSpecBinderOwner::Clause(assertion.clause)
                            && witness.is_none_or(|id| term(id).is_some_and(|t| t.ty == b.ty))
                    })
            }
        };
        if !valid {
            return Err(bad());
        }
        nodes.push(node);
    }
    let mut free: Vec<BTreeSet<u32>> = Vec::new();
    let mut budget = 1_000_000;
    for term in specs.terms() {
        let mut vars = BTreeSet::new();
        let children = match &term.kind {
            T::Binder(id) => {
                vars.insert(id.get());
                vec![]
            }
            T::CheckedAdd { left, right }
            | T::CheckedSub { left, right }
            | T::Equal { left, right }
            | T::LessThan { left, right }
            | T::LessOrEqual { left, right } => vec![*left, *right],
            T::Not(id) | T::CheckedScale { operand: id, .. } => vec![*id],
            T::RangeContains {
                outer_start: a,
                outer_end: b,
                inner_start: c,
                inner_end: d,
            }
            | T::RangeDisjoint {
                left_start: a,
                left_end: b,
                right_start: c,
                right_end: d,
            } => vec![*a, *b, *c, *d],
            T::And(ids) | T::Or(ids) => ids.clone(),
            _ => vec![],
        };
        for id in children {
            if !extend(&mut vars, &free[id.get() as usize], &mut budget) {
                return Err(program_error(VirValidationErrorKind::InvalidSpecTerm(
                    term.id,
                )));
            }
        }
        free.push(vars);
    }
    let roots: Vec<_> = specs
        .clauses()
        .iter()
        .filter_map(|c| match c.kind {
            VirSpecClauseKind::Logic { root } => Some(ScopeNode {
                terms: vec![root.get() as usize],
                children: vec![],
                binder: None,
            }),
            VirSpecClauseKind::Assertion { root } => Some(ScopeNode {
                terms: vec![],
                children: vec![root.get() as usize],
                binder: None,
            }),
            _ => None,
        })
        .collect();
    if !valid_scopes(&free, &nodes, &roots) {
        return Err(program_error(VirValidationErrorKind::InvalidSpecAssertion(
            specs.assertions()[0].id,
        )));
    }
    Ok(())
}

fn valid_pointer(
    unit: &VirUnit,
    clause: &crate::VirSpecClause,
    snapshot: crate::VirSpecSnapshot,
    layout: Option<crate::VirMemoryAccess>,
) -> bool {
    validate_snapshot_type(
        unit,
        clause,
        snapshot,
        |ty| matches!(ty, VirType::Pointer { access } if layout.is_none_or(|expected| access == expected)),
    )
}
