//! Aggregate-storage identities determined before CFG lowering.

use crate::ByteSpan;
use crate::frontend::hir::{HirLocalId, HirNodeId, HirTypeId};

/// Storage for an aggregate constructor or a resource-assignment RHS snapshot.
#[derive(Clone, Copy)]
pub(super) struct ObjectTemporaryStorage {
    pub(super) owner: HirNodeId,
    pub(super) ty: HirTypeId,
    pub(super) span: ByteSpan,
    pub(super) local: HirLocalId,
}

use super::{HirExpression, HirExpressionKind, HirUseMode, HirVisitor, walk_expression};
use std::collections::BTreeSet;

pub(super) fn shared_read_accesses(
    body: &crate::frontend::hir::HirBody,
    memory: &super::LoweredMemorySchema,
    span: ByteSpan,
) -> BTreeSet<crate::VirMemoryAccess> {
    // A shared field read copies into a private slot before extracting its
    // SSA authority. Taking and restoring the source would require write
    // access to a shared container. Each scratch slot is empty again after
    // the take, including on loop backedges.
    struct SharedReads(BTreeSet<HirTypeId>);
    impl<'a> HirVisitor<'a> for SharedReads {
        fn visit_expression(&mut self, expression: &'a HirExpression) {
            if matches!(
                expression.kind,
                HirExpressionKind::Read {
                    mode: HirUseMode::Copy,
                    ref place,
                } if !place.projections.is_empty()
            ) {
                self.0.insert(expression.ty);
            }
            walk_expression(self, expression);
        }
        fn visit_statement(&mut self, statement: &'a super::HirStatement) {
            if let super::HirStatementKind::Match { scrutinee, .. } = &statement.kind {
                self.0.insert(scrutinee.ty);
            }
            super::walk_statement(self, statement);
        }
    }
    let mut reads = SharedReads(BTreeSet::new());
    reads.visit_block(&body.root);
    let mut scratch_accesses = BTreeSet::new();
    for ty in reads.0 {
        let Ok(access) = memory.access(ty, span) else {
            continue;
        };
        if let Ok(shape) = memory.schema().object_shape(access) {
            scratch_accesses.extend(
                shape
                    .resource_leaves()
                    .iter()
                    .filter(|leaf| {
                        leaf.kind() == crate::VirPointerKind::Reference
                            && leaf.mutability() == crate::VirMutability::Const
                    })
                    .map(|leaf| leaf.access()),
            );
        }
    }
    scratch_accesses
}
