//! Shared read-only traversal of structured HIR bodies.
//!
//! The walkers are deliberately exhaustive. Adding a statement, expression,
//! or place projection therefore requires updating traversal once instead of
//! independently maintaining every HIR analysis.

use super::{
    HirBlock, HirExpression, HirExpressionKind, HirForSource, HirPlace, HirProjectionKind,
    HirStatement, HirStatementKind,
};

pub(crate) trait HirVisitor<'hir> {
    fn visit_block(&mut self, block: &'hir HirBlock) {
        walk_block(self, block);
    }

    fn visit_statement(&mut self, statement: &'hir HirStatement) {
        walk_statement(self, statement);
    }

    fn visit_expression(&mut self, expression: &'hir HirExpression) {
        walk_expression(self, expression);
    }

    fn visit_place(&mut self, place: &'hir HirPlace) {
        walk_place(self, place);
    }
}

pub(crate) fn walk_block<'hir, V: HirVisitor<'hir> + ?Sized>(
    visitor: &mut V,
    block: &'hir HirBlock,
) {
    for statement in &block.statements {
        visitor.visit_statement(statement);
    }
}

pub(crate) fn walk_statement<'hir, V: HirVisitor<'hir> + ?Sized>(
    visitor: &mut V,
    statement: &'hir HirStatement,
) {
    match &statement.kind {
        HirStatementKind::Prove { .. }
        | HirStatementKind::Declare { .. }
        | HirStatementKind::Free { .. }
        | HirStatementKind::Break { .. }
        | HirStatementKind::Continue { .. } => {}
        HirStatementKind::Let { value, .. } | HirStatementKind::Evaluate { expression: value } => {
            visitor.visit_expression(value)
        }
        HirStatementKind::Assign { destination, value } => {
            visitor.visit_place(destination);
            visitor.visit_expression(value);
        }
        HirStatementKind::Return { value } => {
            if let Some(value) = value {
                visitor.visit_expression(value);
            }
        }
        HirStatementKind::Block { block } => visitor.visit_block(block),
        HirStatementKind::If {
            condition,
            then_block,
            else_block,
        } => {
            visitor.visit_expression(condition);
            visitor.visit_block(then_block);
            if let Some(else_block) = else_block {
                visitor.visit_block(else_block);
            }
        }
        HirStatementKind::While {
            condition, body, ..
        } => {
            visitor.visit_expression(condition);
            visitor.visit_block(body);
        }
        HirStatementKind::For { source, body, .. } => {
            let HirForSource::IntegerRange { start, end, .. } = source;
            visitor.visit_expression(start);
            visitor.visit_expression(end);
            visitor.visit_block(body);
        }
        HirStatementKind::Match { scrutinee, arms } => {
            visitor.visit_expression(scrutinee);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    visitor.visit_expression(guard);
                }
                visitor.visit_block(&arm.body);
            }
        }
    }
}

pub(crate) fn walk_expression<'hir, V: HirVisitor<'hir> + ?Sized>(
    visitor: &mut V,
    expression: &'hir HirExpression,
) {
    match &expression.kind {
        HirExpressionKind::TupleConstructor { elements }
        | HirExpressionKind::ArrayConstructor { elements } => {
            for element in elements {
                visitor.visit_expression(element);
            }
        }
        HirExpressionKind::ArrayRepeatConstructor { value, .. }
        | HirExpressionKind::PointerOffset { base: value, .. } => {
            visitor.visit_expression(value);
        }
        HirExpressionKind::StructConstructor { fields }
        | HirExpressionKind::EnumConstructor { fields, .. } => {
            for field in fields {
                visitor.visit_expression(&field.value);
            }
        }
        HirExpressionKind::Compare { left, right, .. }
        | HirExpressionKind::PointerDistance {
            begin: left,
            end: right,
        } => {
            visitor.visit_expression(left);
            visitor.visit_expression(right);
        }
        HirExpressionKind::WordAdd { operands, .. } => {
            for operand in operands {
                visitor.visit_expression(operand);
            }
        }
        HirExpressionKind::Read { place, .. }
        | HirExpressionKind::Length { place }
        | HirExpressionKind::OwnerAddress { place }
        | HirExpressionKind::Borrow { place, .. }
        | HirExpressionKind::RawAddress { place, .. } => visitor.visit_place(place),
        HirExpressionKind::Call(call) => {
            for argument in &call.arguments {
                visitor.visit_expression(argument);
            }
        }
        HirExpressionKind::Unit
        | HirExpressionKind::Integer(_)
        | HirExpressionKind::Bool(_)
        | HirExpressionKind::Allocate { .. } => {}
    }
}

pub(crate) fn walk_place<'hir, V: HirVisitor<'hir> + ?Sized>(
    visitor: &mut V,
    place: &'hir HirPlace,
) {
    for projection in &place.projections {
        match &projection.kind {
            HirProjectionKind::DynamicIndex { index } => visitor.visit_expression(index),
            HirProjectionKind::Slice { start, end } => {
                for bound in start.iter().chain(end) {
                    visitor.visit_expression(bound);
                }
            }
            HirProjectionKind::Dereference
            | HirProjectionKind::Field { .. }
            | HirProjectionKind::TupleElement { .. }
            | HirProjectionKind::ConstantIndex { .. }
            | HirProjectionKind::Downcast { .. } => {}
        }
    }
}
