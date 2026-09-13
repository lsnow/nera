//! Canonical program-wide HIR node numbering.

use super::super::FrontendFailure;
use super::{
    HirBody, HirExpression, HirExpressionKind, HirForSource, HirNodeId, HirPattern, HirPatternKind,
    HirPlace, HirProjectionKind, HirStatement, HirStatementKind,
};
use crate::ByteSpan;

pub(super) const UNASSIGNED_NODE_ID: HirNodeId = HirNodeId::new(u32::MAX);

pub(super) fn assign_body_node_ids(
    body: &mut HirBody,
    next: &mut u32,
    span: ByteSpan,
) -> Result<(), FrontendFailure> {
    visit_block_mut(&mut body.root, &mut |id| {
        *id = HirNodeId::new(*next);
        *next = next
            .checked_add(1)
            .ok_or_else(|| FrontendFailure::elaboration(span, "too many HIR nodes"))?;
        Ok(())
    })
}

pub(super) fn validate_body_node_ids(
    body: &HirBody,
    next: &mut u32,
) -> Result<(), (HirNodeId, HirNodeId)> {
    visit_block(&body.root, &mut |found| {
        let expected = HirNodeId::new(*next);
        if found != expected {
            return Err((expected, found));
        }
        *next = next.checked_add(1).ok_or((expected, found))?;
        Ok(())
    })
}

fn visit_block_mut<E>(
    block: &mut super::HirBlock,
    visit: &mut impl FnMut(&mut HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    for statement in &mut block.statements {
        visit_statement_mut(statement, visit)?;
    }
    Ok(())
}

fn visit_statement_mut<E>(
    statement: &mut HirStatement,
    visit: &mut impl FnMut(&mut HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    visit(&mut statement.id)?;
    match &mut statement.kind {
        HirStatementKind::Let { value, .. } => visit_expression_mut(value, visit),
        HirStatementKind::Assign { destination, value } => {
            visit_place_mut(destination, visit)?;
            visit_expression_mut(value, visit)
        }
        HirStatementKind::Return { value } => {
            if let Some(value) = value {
                visit_expression_mut(value, visit)?;
            }
            Ok(())
        }
        HirStatementKind::Evaluate { expression } => visit_expression_mut(expression, visit),
        HirStatementKind::Block { block } => visit_block_mut(block, visit),
        HirStatementKind::If {
            condition,
            then_block,
            else_block,
        } => {
            visit_expression_mut(condition, visit)?;
            visit_block_mut(then_block, visit)?;
            if let Some(block) = else_block {
                visit_block_mut(block, visit)?;
            }
            Ok(())
        }
        HirStatementKind::While {
            condition, body, ..
        } => {
            visit_expression_mut(condition, visit)?;
            visit_block_mut(body, visit)
        }
        HirStatementKind::For {
            pattern,
            source,
            body,
            ..
        } => {
            visit_for_source_mut(source, visit)?;
            visit_pattern_mut(pattern, visit)?;
            visit_block_mut(body, visit)
        }
        HirStatementKind::Match { scrutinee, arms } => {
            visit_expression_mut(scrutinee, visit)?;
            for arm in arms {
                visit_pattern_mut(&mut arm.pattern, visit)?;
                if let Some(guard) = &mut arm.guard {
                    visit_expression_mut(guard, visit)?;
                }
                visit_block_mut(&mut arm.body, visit)?;
            }
            Ok(())
        }
        HirStatementKind::Prove { .. }
        | HirStatementKind::Declare { .. }
        | HirStatementKind::Free { .. }
        | HirStatementKind::Break { .. }
        | HirStatementKind::Continue { .. } => Ok(()),
    }
}

fn visit_for_source_mut<E>(
    source: &mut HirForSource,
    visit: &mut impl FnMut(&mut HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    match source {
        HirForSource::IntegerRange { start, end, .. } => {
            visit_expression_mut(start, visit)?;
            visit_expression_mut(end, visit)
        }
    }
}

fn visit_expression_mut<E>(
    expression: &mut HirExpression,
    visit: &mut impl FnMut(&mut HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    visit(&mut expression.id)?;
    match &mut expression.kind {
        HirExpressionKind::TupleConstructor { elements }
        | HirExpressionKind::ArrayConstructor { elements } => {
            for element in elements {
                visit_expression_mut(element, visit)?;
            }
            Ok(())
        }
        HirExpressionKind::ArrayRepeatConstructor { value, .. }
        | HirExpressionKind::PointerOffset { base: value, .. } => {
            visit_expression_mut(value, visit)
        }
        HirExpressionKind::StructConstructor { fields }
        | HirExpressionKind::EnumConstructor { fields, .. } => {
            for field in fields {
                visit_expression_mut(&mut field.value, visit)?;
            }
            Ok(())
        }
        HirExpressionKind::Compare { left, right, .. }
        | HirExpressionKind::PointerDistance {
            begin: left,
            end: right,
        } => {
            visit_expression_mut(left, visit)?;
            visit_expression_mut(right, visit)
        }
        HirExpressionKind::WordAdd { operands, .. } => {
            for operand in operands {
                visit_expression_mut(operand, visit)?;
            }
            Ok(())
        }
        HirExpressionKind::Read { place, .. }
        | HirExpressionKind::Length { place }
        | HirExpressionKind::OwnerAddress { place }
        | HirExpressionKind::Borrow { place, .. }
        | HirExpressionKind::RawAddress { place, .. } => visit_place_mut(place, visit),
        HirExpressionKind::Call(call) => {
            for argument in &mut call.arguments {
                visit_expression_mut(argument, visit)?;
            }
            Ok(())
        }
        HirExpressionKind::Unit
        | HirExpressionKind::Integer(_)
        | HirExpressionKind::Bool(_)
        | HirExpressionKind::Allocate { .. } => Ok(()),
    }
}

fn visit_place_mut<E>(
    place: &mut HirPlace,
    visit: &mut impl FnMut(&mut HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    visit(&mut place.id)?;
    for projection in &mut place.projections {
        match &mut projection.kind {
            HirProjectionKind::DynamicIndex { index } => visit_expression_mut(index, visit)?,
            HirProjectionKind::Slice { start, end } => {
                if let Some(start) = start {
                    visit_expression_mut(start, visit)?;
                }
                if let Some(end) = end {
                    visit_expression_mut(end, visit)?;
                }
            }
            HirProjectionKind::Dereference
            | HirProjectionKind::Field { .. }
            | HirProjectionKind::TupleElement { .. }
            | HirProjectionKind::ConstantIndex { .. }
            | HirProjectionKind::Downcast { .. } => {}
        }
    }
    Ok(())
}

fn visit_block<E>(
    block: &super::HirBlock,
    visit: &mut impl FnMut(HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    for statement in &block.statements {
        visit_statement(statement, visit)?;
    }
    Ok(())
}

fn visit_statement<E>(
    statement: &HirStatement,
    visit: &mut impl FnMut(HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    visit(statement.id)?;
    match &statement.kind {
        HirStatementKind::Let { value, .. } => visit_expression(value, visit),
        HirStatementKind::Assign { destination, value } => {
            visit_place(destination, visit)?;
            visit_expression(value, visit)
        }
        HirStatementKind::Return { value } => {
            if let Some(value) = value {
                visit_expression(value, visit)?;
            }
            Ok(())
        }
        HirStatementKind::Evaluate { expression } => visit_expression(expression, visit),
        HirStatementKind::Block { block } => visit_block(block, visit),
        HirStatementKind::If {
            condition,
            then_block,
            else_block,
        } => {
            visit_expression(condition, visit)?;
            visit_block(then_block, visit)?;
            if let Some(block) = else_block {
                visit_block(block, visit)?;
            }
            Ok(())
        }
        HirStatementKind::While {
            condition, body, ..
        } => {
            visit_expression(condition, visit)?;
            visit_block(body, visit)
        }
        HirStatementKind::For {
            pattern,
            source,
            body,
            ..
        } => {
            let HirForSource::IntegerRange { start, end, .. } = source;
            visit_expression(start, visit)?;
            visit_expression(end, visit)?;
            visit_pattern(pattern, visit)?;
            visit_block(body, visit)
        }
        HirStatementKind::Match { scrutinee, arms } => {
            visit_expression(scrutinee, visit)?;
            for arm in arms {
                visit_pattern(&arm.pattern, visit)?;
                if let Some(guard) = &arm.guard {
                    visit_expression(guard, visit)?;
                }
                visit_block(&arm.body, visit)?;
            }
            Ok(())
        }
        HirStatementKind::Prove { .. }
        | HirStatementKind::Declare { .. }
        | HirStatementKind::Free { .. }
        | HirStatementKind::Break { .. }
        | HirStatementKind::Continue { .. } => Ok(()),
    }
}

fn visit_expression<E>(
    expression: &HirExpression,
    visit: &mut impl FnMut(HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    visit(expression.id)?;
    match &expression.kind {
        HirExpressionKind::TupleConstructor { elements }
        | HirExpressionKind::ArrayConstructor { elements } => {
            for element in elements {
                visit_expression(element, visit)?;
            }
            Ok(())
        }
        HirExpressionKind::ArrayRepeatConstructor { value, .. }
        | HirExpressionKind::PointerOffset { base: value, .. } => visit_expression(value, visit),
        HirExpressionKind::StructConstructor { fields }
        | HirExpressionKind::EnumConstructor { fields, .. } => {
            for field in fields {
                visit_expression(&field.value, visit)?;
            }
            Ok(())
        }
        HirExpressionKind::Compare { left, right, .. }
        | HirExpressionKind::PointerDistance {
            begin: left,
            end: right,
        } => {
            visit_expression(left, visit)?;
            visit_expression(right, visit)
        }
        HirExpressionKind::WordAdd { operands, .. } => {
            for operand in operands {
                visit_expression(operand, visit)?;
            }
            Ok(())
        }
        HirExpressionKind::Read { place, .. }
        | HirExpressionKind::Length { place }
        | HirExpressionKind::OwnerAddress { place }
        | HirExpressionKind::Borrow { place, .. }
        | HirExpressionKind::RawAddress { place, .. } => visit_place(place, visit),
        HirExpressionKind::Call(call) => {
            for argument in &call.arguments {
                visit_expression(argument, visit)?;
            }
            Ok(())
        }
        HirExpressionKind::Unit
        | HirExpressionKind::Integer(_)
        | HirExpressionKind::Bool(_)
        | HirExpressionKind::Allocate { .. } => Ok(()),
    }
}

fn visit_place<E>(
    place: &HirPlace,
    visit: &mut impl FnMut(HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    visit(place.id)?;
    for projection in &place.projections {
        match &projection.kind {
            HirProjectionKind::DynamicIndex { index } => visit_expression(index, visit)?,
            HirProjectionKind::Slice { start, end } => {
                if let Some(start) = start {
                    visit_expression(start, visit)?;
                }
                if let Some(end) = end {
                    visit_expression(end, visit)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn visit_pattern<E>(
    pattern: &HirPattern,
    visit: &mut impl FnMut(HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    visit(pattern.id)?;
    match &pattern.kind {
        HirPatternKind::Tuple(patterns)
        | HirPatternKind::Variant {
            fields: patterns, ..
        } => {
            for pattern in patterns {
                visit_pattern(pattern, visit)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn visit_pattern_mut<E>(
    pattern: &mut HirPattern,
    visit: &mut impl FnMut(&mut HirNodeId) -> Result<(), E>,
) -> Result<(), E> {
    visit(&mut pattern.id)?;
    match &mut pattern.kind {
        HirPatternKind::Tuple(patterns)
        | HirPatternKind::Variant {
            fields: patterns, ..
        } => {
            for pattern in patterns {
                visit_pattern_mut(pattern, visit)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HirProgram, HirProgramTables, SourceFile, analyze};

    fn accepted(name: &str, source: &str) -> HirProgram {
        analyze(&SourceFile::from_text(name, source))
            .hir()
            .expect("fixture source is accepted")
            .clone()
    }

    fn tables(program: &HirProgram) -> HirProgramTables {
        HirProgramTables {
            data_layout: program.data_layout(),
            entry_module: program.entry_module_id(),
            entry_function: program.entry_function_id(),
            modules: program.modules().to_vec(),
            types: program.types().to_vec(),
            type_capabilities: program
                .types()
                .iter()
                .map(|ty| {
                    program
                        .type_capabilities(ty.id)
                        .expect("validated capability")
                })
                .collect(),
            layouts: program.layouts().to_vec(),
            fields: program.fields().to_vec(),
            variants: program.variants().to_vec(),
            generic_parameters: program.generic_parameters().to_vec(),
            regions: program.regions().to_vec(),
            region_constraints: program.region_constraints().to_vec(),
            functions: program.functions().to_vec(),
            contracts: program.contracts().to_vec(),
            predicates: program.predicates().to_vec(),
            specs: program.specs().clone(),
        }
    }

    fn ids(program: &HirProgram) -> Vec<HirNodeId> {
        let mut ids = Vec::new();
        for function in program.functions() {
            if let Some(body) = function.body() {
                visit_block(&body.root, &mut |id| {
                    ids.push(id);
                    Ok::<_, ()>(())
                })
                .expect("infallible collection");
            }
        }
        ids
    }

    #[test]
    fn identities_are_dense_program_wide_and_replay_stable() {
        let source = include_str!("../../../spec/cases/aggregate/surface.nera");
        let first = accepted("surface.nera", source);
        let second = accepted("surface.nera", source);
        assert_eq!(first, second);

        let found = ids(&first);
        let expected = (0..found.len())
            .map(|raw| HirNodeId::new(raw as u32))
            .collect::<Vec<_>>();
        assert_eq!(found, expected);

        let first_function_count = first.functions()[0]
            .body()
            .map(|body| {
                let mut count = 0;
                visit_block(&body.root, &mut |_| {
                    count += 1;
                    Ok::<_, ()>(())
                })
                .expect("infallible count");
                count
            })
            .expect("main has a body");
        assert_eq!(
            first.functions()[1]
                .body()
                .expect("index body")
                .root
                .statements[0]
                .id
                .get() as usize,
            first_function_count,
            "the second function continues the program-wide sequence"
        );
    }

    #[test]
    fn malformed_statement_expression_place_and_pattern_ids_fail_closed() {
        let direct = accepted(
            "direct.nera",
            include_str!("../../../spec/cases/control-flow/direct-call.nera"),
        );
        let mut duplicate_expression = tables(&direct);
        let statement = &mut duplicate_expression.functions[0]
            .body
            .as_mut()
            .expect("body")
            .root
            .statements[0];
        let HirStatementKind::Return { value: Some(value) } = &mut statement.kind else {
            panic!("fixture return")
        };
        value.id = statement.id;
        let error = HirProgram::from_tables(duplicate_expression).expect_err("duplicate node ID");
        assert_eq!(error.table(), "node");

        let mut wrong_statement = tables(&direct);
        wrong_statement.functions[0]
            .body
            .as_mut()
            .expect("body")
            .root
            .statements[0]
            .id = HirNodeId::new(99);
        assert_eq!(
            HirProgram::from_tables(wrong_statement)
                .expect_err("non-dense statement ID")
                .table(),
            "node"
        );

        let aggregate = accepted(
            "surface.nera",
            include_str!("../../../spec/cases/aggregate/surface.nera"),
        );
        let mut swapped_statements = tables(&aggregate);
        let statements = &mut swapped_statements.functions[0]
            .body
            .as_mut()
            .expect("body")
            .root
            .statements;
        let first = statements[0].id;
        statements[0].id = statements[1].id;
        statements[1].id = first;
        assert_eq!(
            HirProgram::from_tables(swapped_statements)
                .expect_err("swapped preorder IDs")
                .table(),
            "node"
        );

        let mut duplicate_place = tables(&aggregate);
        let statement = &mut duplicate_place.functions[0]
            .body
            .as_mut()
            .expect("body")
            .root
            .statements[3];
        let HirStatementKind::Assign { destination, .. } = &mut statement.kind else {
            panic!("fixture assignment")
        };
        destination.id = statement.id;
        assert_eq!(
            HirProgram::from_tables(duplicate_place)
                .expect_err("duplicate place ID")
                .table(),
            "node"
        );

        let control = accepted(
            "for.nera",
            include_str!("../../../spec/cases/control-flow/for-range.nera"),
        );
        let mut duplicate_pattern = tables(&control);
        let statement = &mut duplicate_pattern.functions[0]
            .body
            .as_mut()
            .expect("body")
            .root
            .statements[1];
        let HirStatementKind::For { pattern, .. } = &mut statement.kind else {
            panic!("fixture for")
        };
        pattern.id = statement.id;
        assert_eq!(
            HirProgram::from_tables(duplicate_pattern)
                .expect_err("duplicate pattern ID")
                .table(),
            "node"
        );
    }
}
