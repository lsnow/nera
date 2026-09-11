//! Lexical cleanup planning independent from CFG edge emission.

use std::collections::BTreeSet;

use super::draft::{PendingCleanup, PendingCleanupKind};
use super::invalid_hir;
use crate::ByteSpan;
use crate::frontend::FrontendFailure;
use crate::frontend::hir::HirScopeId;
use crate::vir::{SpannedVirInstruction, VirInstruction, VirMemorySchema};

/// Select the explicit cleanup effect from canonical type capabilities. This
/// does not claim that the value is complete: ObjectDrop checks actual present
/// resource leaves, and the verifier independently checks every precondition.
pub(super) fn plan_effect(
    memory: &VirMemorySchema,
    intent: &PendingCleanup,
) -> Result<SpannedVirInstruction, FrontendFailure> {
    let object = intent.identity.object;
    let span = intent.identity.source_span;
    let capability = memory
        .type_capabilities(object.access.ty)
        .ok_or_else(|| invalid_hir(span))?;
    if !memory.resolves_access(object.access) {
        return Err(invalid_hir(span));
    }
    let shape = memory
        .object_shape(object.access)
        .map_err(|_| invalid_hir(span))?;
    let instruction = match intent.kind {
        PendingCleanupKind::OwnedAllocation { condition } => VirInstruction::DropOwn {
            pointer: object.pointer,
            permission: object.permission,
            condition,
        },
        PendingCleanupKind::Object { condition } => match capability.drop {
            crate::DropCapability::TrivialDrop if shape.resource_leaves().is_empty() => {
                if condition.is_some() {
                    return Err(FrontendFailure::unsupported(
                        span,
                        "conditional retirement of trivial storage requires explicit control flow",
                    ));
                }
                VirInstruction::ObjectDeinitialize {
                    pointer: object.pointer,
                    permission: object.permission,
                    access: object.access,
                }
            }
            crate::DropCapability::TrivialDrop | crate::DropCapability::BuiltinDrop => {
                VirInstruction::ObjectDrop {
                    pointer: object.pointer,
                    permission: object.permission,
                    access: object.access,
                    condition: condition.ok_or_else(|| {
                        FrontendFailure::unsupported(
                            span,
                            "resource cleanup requires an explicit presence condition",
                        )
                    })?,
                }
            }
            _ => {
                return Err(FrontendFailure::unsupported(
                    span,
                    "cleanup is not supported for this type capability",
                ));
            }
        },
    };
    Ok(SpannedVirInstruction {
        instruction,
        source_span: span,
    })
}

/// Scopes crossed by one fallthrough, return, break or continue edge, ordered
/// from innermost to outermost for deterministic cleanup emission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ScopeExitPlan {
    leaving_scopes: Vec<HirScopeId>,
}

impl ScopeExitPlan {
    pub(super) fn new(
        active_scopes: &[HirScopeId],
        retained_scope: Option<HirScopeId>,
        source_span: ByteSpan,
    ) -> Result<Self, FrontendFailure> {
        let unique_scopes: BTreeSet<_> = active_scopes.iter().copied().collect();
        if active_scopes.is_empty() || unique_scopes.len() != active_scopes.len() {
            return Err(invalid_hir(source_span));
        }
        let retained_count = match retained_scope {
            Some(scope) => active_scopes
                .iter()
                .rposition(|candidate| *candidate == scope)
                .map(|index| index + 1)
                .ok_or_else(|| invalid_hir(source_span))?,
            None => 0,
        };
        Ok(Self {
            leaving_scopes: active_scopes[retained_count..]
                .iter()
                .rev()
                .copied()
                .collect(),
        })
    }

    pub(super) fn leaving_scopes(&self) -> &[HirScopeId] {
        &self.leaving_scopes
    }
}
