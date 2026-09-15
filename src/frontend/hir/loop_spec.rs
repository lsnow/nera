//! Lexical loop lookup shared by typed Spec validation and lowering.
use super::*;

pub(in crate::frontend) fn find_loop(
    block: &HirBlock,
    id: HirLoopId,
) -> Option<(&HirStatement, &HirBlock, Option<HirLocalId>)> {
    for statement in &block.statements {
        match &statement.kind {
            HirStatementKind::While { loop_id, body, .. } => {
                if *loop_id == id {
                    return Some((statement, body, None));
                }
                if let Some(found) = find_loop(body, id) {
                    return Some(found);
                }
            }
            HirStatementKind::For {
                loop_id,
                body,
                pattern,
                ..
            } => {
                if *loop_id == id {
                    let HirPatternKind::Binding { local, .. } = pattern.kind else {
                        return None;
                    };
                    return Some((statement, body, Some(local)));
                }
                if let Some(found) = find_loop(body, id) {
                    return Some(found);
                }
            }
            HirStatementKind::Block { block } => {
                if let Some(f) = find_loop(block, id) {
                    return Some(f);
                }
            }
            HirStatementKind::If {
                then_block,
                else_block,
                ..
            } => {
                if let Some(f) = find_loop(then_block, id) {
                    return Some(f);
                }
                if let Some(f) = else_block.as_ref().and_then(|b| find_loop(b, id)) {
                    return Some(f);
                }
            }
            HirStatementKind::Match { arms, .. } => {
                for arm in arms {
                    if let Some(f) = find_loop(&arm.body, id) {
                        return Some(f);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

pub(in crate::frontend) fn visible_at_loop(
    block: &HirBlock,
    id: HirLoopId,
    scope: HirScopeId,
) -> bool {
    if find_loop(block, id).is_none() {
        return false;
    }
    if block.scope == scope {
        return true;
    }
    for s in &block.statements {
        let found = match &s.kind {
            HirStatementKind::While { body, .. }
            | HirStatementKind::For { body, .. }
            | HirStatementKind::Block { block: body } => visible_at_loop(body, id, scope),
            HirStatementKind::If {
                then_block,
                else_block,
                ..
            } => {
                visible_at_loop(then_block, id, scope)
                    || else_block
                        .as_ref()
                        .is_some_and(|b| visible_at_loop(b, id, scope))
            }
            HirStatementKind::Match { arms, .. } => {
                arms.iter().any(|a| visible_at_loop(&a.body, id, scope))
            }
            _ => false,
        };
        if found {
            return true;
        }
    }
    false
}
