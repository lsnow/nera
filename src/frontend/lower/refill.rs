//! Partial resource refill reuses canonical leaf cleanup and transfer effects.
//! No path-presence table lives here: actual presence/authority is checked by
//! the independent VIR consumers, including at control-flow joins.

use super::{
    DraftObjectIdentity, DraftSourceIdentity, LoweredObject, Lowerer, PendingCleanupKind,
    invalid_hir,
};
use crate::ByteSpan;
use crate::frontend::{
    FrontendFailure,
    hir::{HirBlock, HirExpression, HirExpressionKind, HirProgram, HirStatementKind, HirTypeKind},
};

/// A read RHS must be captured before destination cleanup (including aliasing
/// and self-assignment). Constructors/calls already own expression temporaries.
pub(super) fn collect_assignment_sources<'hir>(
    hir: &HirProgram,
    block: &'hir HirBlock,
    output: &mut Vec<&'hir HirExpression>,
) {
    for statement in &block.statements {
        match &statement.kind {
            HirStatementKind::Assign { value, .. }
                if matches!(value.kind, HirExpressionKind::Read { .. })
                    && hir
                        .type_capabilities(value.ty)
                        .is_some_and(|cap| cap.contains_resource)
                    && matches!(
                        hir.type_kind(value.ty),
                        Some(
                            HirTypeKind::Array { .. }
                                | HirTypeKind::Tuple(_)
                                | HirTypeKind::Struct { .. }
                                | HirTypeKind::Enum { .. }
                        )
                    ) =>
            {
                output.push(value)
            }
            HirStatementKind::Block { block }
            | HirStatementKind::While { body: block, .. }
            | HirStatementKind::For { body: block, .. } => {
                collect_assignment_sources(hir, block, output)
            }
            HirStatementKind::If {
                then_block,
                else_block,
                ..
            } => {
                collect_assignment_sources(hir, then_block, output);
                if let Some(block) = else_block {
                    collect_assignment_sources(hir, block, output);
                }
            }
            HirStatementKind::Match { arms, .. } => {
                for arm in arms {
                    collect_assignment_sources(hir, &arm.body, output);
                }
            }
            _ => {}
        }
    }
}

impl Lowerer<'_> {
    pub(super) fn emit_resource_object_assignment(
        &mut self,
        mut destination: LoweredObject,
        mut source: LoweredObject,
        expression: &HirExpression,
        span: ByteSpan,
    ) -> Result<bool, FrontendFailure> {
        let shape = self
            .memory
            .schema()
            .object_shape(destination.access)
            .map_err(|_| invalid_hir(span))?;
        if shape.resource_leaves().is_empty() {
            return Ok(false);
        }
        let tagged = !shape.variants().is_empty();
        let identity = DraftSourceIdentity::HirNode(expression.id);
        if matches!(expression.kind, HirExpressionKind::Read { .. }) {
            let temporary = self.expression_object_temporary(expression, source.access)?;
            self.emit_object_assignment(
                temporary,
                source,
                super::object_source_mode(expression)?,
                identity,
                span,
            )?;
            source = self.storage_object(
                self.object_storage_local(temporary)
                    .ok_or_else(|| invalid_hir(span))?,
                span,
            )?;
            if tagged && let Some(local) = self.object_storage_local(destination) {
                // A self-move retires the source representation while capturing
                // the RHS. Consult the updated flag, not the pre-RHS snapshot.
                destination.drop_flag = self.storage_object(local, span)?.drop_flag;
            }
        }

        // A root enum's flag denotes an established representation, not a
        // complete payload. Do not read a retired tag after a whole move.
        // Variant-free partial storage has canonical empty slots even without
        // a whole-object flag and can always run its present-leaf cleanup.
        let condition = if tagged {
            match destination.drop_flag {
                Some(condition) => condition,
                None => self.lower_generated_drop_flag(true, span)?,
            }
        } else {
            self.lower_generated_drop_flag(true, span)?
        };
        self.cfg.emit_cleanup(
            PendingCleanupKind::Object {
                condition: Some(condition),
            },
            DraftObjectIdentity {
                pointer: destination.pointer,
                permission: destination.permission,
                access: destination.access,
            },
            identity,
            span,
        )?;
        // Destination cleanup is already explicit. Suppress a second whole
        // cleanup; its old flag is not proof that a partial object is complete.
        self.emit_object_assignment(
            LoweredObject {
                drop_flag: None,
                ..destination
            },
            source,
            crate::VirObjectSourceMode::Move,
            identity,
            span,
        )?;
        if destination.drop_flag.is_some() {
            self.set_object_drop_flag(destination, true, span)?;
        }
        Ok(true)
    }
}
