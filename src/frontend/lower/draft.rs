//! Private, non-serializable VIR construction state.
//!
//! Draft values are owned exclusively by HIR lowering and post-CFG passes.
//! They deliberately have no dump, validation, resolution or consumer API.

use crate::ByteSpan;
use crate::frontend::hir::{HirFunctionId, HirLocalId, HirNodeId};
use crate::vir::{
    SpannedVirInstruction, SpannedVirTerminator, VirBasicBlock, VirBlockId, VirBorrowRegionId,
    VirLoanEffect, VirMemoryAccess, VirSourceMapEntry, VirValue, VirValueId,
};

/// Canonical HIR region relation retained until loan-end planning completes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct DraftRegionConstraint {
    pub(super) subregion: VirBorrowRegionId,
    pub(super) superregion: VirBorrowRegionId,
}

/// Stable producer identity retained while one effect is still pending.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DraftSourceIdentity {
    HirNode(HirNodeId),
    FunctionEntry(HirFunctionId),
    LocalCleanup(HirLocalId),
}

/// Canonical addressed object retained independently of the pending effect.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct DraftObjectIdentity {
    pub(super) pointer: VirValueId,
    pub(super) permission: VirValueId,
    pub(super) access: VirMemoryAccess,
}

/// Cross-pass identity which must agree with the operation being materialized.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct DraftEffectIdentity {
    pub(super) source: DraftSourceIdentity,
    pub(super) object: DraftObjectIdentity,
    pub(super) source_span: ByteSpan,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PendingAssignmentSource {
    Scalar {
        value: VirValueId,
    },
    Object {
        pointer: VirValueId,
        permission: VirValueId,
        mode: crate::VirObjectSourceMode,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PendingAssignment {
    pub(super) identity: DraftEffectIdentity,
    pub(super) destination: VirValueId,
    pub(super) destination_permission: VirValueId,
    pub(super) access: VirMemoryAccess,
    pub(super) source: PendingAssignmentSource,
    pub(super) source_span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PendingCleanup {
    pub(super) identity: DraftEffectIdentity,
    pub(super) kind: PendingCleanupKind,
}

/// Cleanup policy, not a preselected runtime instruction or initialization fact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PendingCleanupKind {
    OwnedAllocation { condition: VirValueId },
    Object { condition: Option<VirValueId> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct PendingLoanEnd {
    pub(super) identity: DraftEffectIdentity,
    pub(super) effect: PendingLoanEndEffect,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PendingLoanEndEffect {
    Static(VirLoanEffect),
    Authority(crate::VirLoanAuthorityEffect),
}

impl PendingLoanEndEffect {
    pub(super) const fn source_pointer(self) -> VirValueId {
        match self {
            Self::Static(effect) => effect.source_pointer,
            Self::Authority(effect) => effect.source_pointer,
        }
    }

    pub(super) const fn source_permission(self) -> VirValueId {
        match self {
            Self::Static(effect) => effect.source_permission,
            Self::Authority(effect) => effect.source_permission,
        }
    }

    pub(super) const fn reference(self) -> VirMemoryAccess {
        match self {
            Self::Static(effect) => effect.reference,
            Self::Authority(effect) => effect.reference,
        }
    }

    pub(super) const fn loan(self) -> Option<crate::VirLoanId> {
        match self {
            Self::Static(effect) => Some(effect.loan),
            Self::Authority(_) => None,
        }
    }

    pub(super) const fn instruction(self) -> crate::VirInstruction {
        match self {
            Self::Static(effect) => crate::VirInstruction::LoanEnd { effect },
            Self::Authority(effect) => crate::VirInstruction::LoanEndAuthority { effect },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum PendingEffect {
    Assignment(PendingAssignment),
    Cleanup(PendingCleanup),
    LoanEnd(PendingLoanEnd),
}

impl PendingEffect {
    pub(super) const fn identity(&self) -> DraftEffectIdentity {
        match self {
            Self::Assignment(effect) => effect.identity,
            Self::Cleanup(effect) => effect.identity,
            Self::LoanEnd(effect) => effect.identity,
        }
    }

    /// Returns the already-determined runtime effect used by earlier analyses.
    /// Assignment and cleanup are excluded: the initialization pass must select
    /// their canonical effects together, in program order.
    pub(super) fn determined_instruction(&self) -> Option<SpannedVirInstruction> {
        match self {
            Self::Assignment(_) => None,
            Self::Cleanup(_) => None,
            Self::LoanEnd(effect) => Some(SpannedVirInstruction {
                instruction: effect.effect.instruction(),
                source_span: effect.identity.source_span,
            }),
        }
    }

    pub(super) fn has_consistent_identity(&self) -> bool {
        let identity = self.identity();
        match self {
            Self::Assignment(effect) => {
                effect.source_span == identity.source_span
                    && effect.destination == identity.object.pointer
                    && effect.destination_permission == identity.object.permission
                    && effect.access == identity.object.access
            }
            // Cleanup has one canonical identity, with no duplicated operands
            // that can disagree before planning.
            Self::Cleanup(_) => true,
            Self::LoanEnd(effect) => {
                effect.effect.source_pointer() == identity.object.pointer
                    && effect.effect.source_permission() == identity.object.permission
                    && effect.effect.reference() == identity.object.access
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum DraftInstruction {
    Canonical(Box<SpannedVirInstruction>),
    Pending(PendingEffect),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DraftBlock {
    pub(super) id: VirBlockId,
    pub(super) parameters: Vec<VirValue>,
    pub(super) instructions: Vec<DraftInstruction>,
    pub(super) terminator: Option<SpannedVirTerminator>,
    pub(super) source_span: ByteSpan,
}

/// Complete CFG topology with effects that still require post-CFG planning.
#[derive(Clone)]
pub(super) struct DraftFunctionBody {
    pub(super) blocks: Vec<DraftBlock>,
    pub(super) source_map_entries: Vec<VirSourceMapEntry>,
}

/// Tests use this helper to prove that no pending effect can be represented by
/// a canonical block. Production reaches it only through the fixed pass list.
pub(super) fn seal_blocks(blocks: Vec<DraftBlock>) -> Result<Vec<VirBasicBlock>, DraftSealError> {
    blocks
        .into_iter()
        .map(|block| {
            let instructions = block
                .instructions
                .into_iter()
                .map(|instruction| match instruction {
                    DraftInstruction::Canonical(instruction) => Ok(*instruction),
                    DraftInstruction::Pending(effect) => Err(DraftSealError::PendingEffect {
                        block: block.id,
                        source_span: effect.identity().source_span,
                    }),
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(VirBasicBlock {
                id: block.id,
                parameters: block.parameters,
                instructions,
                terminator: block
                    .terminator
                    .ok_or(DraftSealError::MissingTerminator(block.id))?,
                source_span: block.source_span,
            })
        })
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DraftSealError {
    PendingEffect {
        block: VirBlockId,
        source_span: ByteSpan,
    },
    MissingTerminator(VirBlockId),
}
