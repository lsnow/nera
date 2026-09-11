//! Fixed post-CFG effect pipeline.
//!
//! The pass list is deliberately closed and ordered. A draft body can become
//! canonical VIR only after every pass has run exactly once and sealing proves
//! that no pending operation remains.

use super::assignment;
use super::draft::{
    DraftBlock, DraftInstruction, DraftRegionConstraint, DraftSealError, PendingEffect, seal_blocks,
};
use super::loan_end::{self, LoanEndPlanningError};
use super::unit::{CanonicalLoweredFunction, DraftLoweredFunction, seal_function};
use crate::ByteSpan;
use crate::frontend::FrontendFailure;
use crate::vir::{VirBasicBlock, VirMemorySchema};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PostCfgPass {
    InitializationEffects,
    LoanEndEffects,
    Seal,
}

pub(super) const POST_CFG_PASSES: &[PostCfgPass] = &[
    PostCfgPass::InitializationEffects,
    PostCfgPass::LoanEndEffects,
    PostCfgPass::Seal,
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum PostCfgError {
    UnexpectedPass {
        expected: Option<PostCfgPass>,
        found: PostCfgPass,
    },
    MissingPass(PostCfgPass),
    InvalidPendingEffect(ByteSpan),
    PendingEffectLeak(DraftSealError),
    InitializationPlanning(FrontendFailure),
    LoanEndPlanning(LoanEndPlanningError),
}

struct PassLedger {
    next: usize,
}

impl PassLedger {
    const fn new() -> Self {
        Self { next: 0 }
    }

    fn enter(&mut self, pass: PostCfgPass) -> Result<(), PostCfgError> {
        let expected = POST_CFG_PASSES.get(self.next).copied();
        if expected != Some(pass) {
            return Err(PostCfgError::UnexpectedPass {
                expected,
                found: pass,
            });
        }
        self.next += 1;
        Ok(())
    }

    fn finish(self) -> Result<(), PostCfgError> {
        match POST_CFG_PASSES.get(self.next).copied() {
            Some(pass) => Err(PostCfgError::MissingPass(pass)),
            None => Ok(()),
        }
    }
}

pub(super) fn canonicalize_function(
    memory: &VirMemorySchema,
    mut draft: DraftLoweredFunction,
) -> Result<CanonicalLoweredFunction, FrontendFailure> {
    let source_span = draft.source_span;
    let blocks = run_passes(
        draft.id,
        memory,
        std::mem::take(&mut draft.body.blocks),
        &draft.region_constraints,
        &mut draft.body.source_map_entries,
        POST_CFG_PASSES,
        source_span,
        Some(&draft.abi),
    )
    .map_err(|error| pass_failure(error, source_span))?;
    Ok(seal_function(draft, blocks))
}

#[cfg(test)]
pub(super) fn canonicalize_body_for_test(
    memory: &VirMemorySchema,
    mut body: super::draft::DraftFunctionBody,
    source_span: ByteSpan,
) -> Result<(Vec<VirBasicBlock>, Vec<crate::vir::VirSourceMapEntry>), FrontendFailure> {
    let blocks = run_passes(
        crate::VirFunctionId::new(0),
        memory,
        std::mem::take(&mut body.blocks),
        &[],
        &mut body.source_map_entries,
        POST_CFG_PASSES,
        source_span,
        None,
    )
    .map_err(|error| pass_failure(error, source_span))?;
    Ok((blocks, body.source_map_entries))
}

fn pass_failure(error: PostCfgError, source_span: ByteSpan) -> FrontendFailure {
    let (diagnostic_span, message) = match error {
        PostCfgError::InitializationPlanning(failure) => return failure,
        PostCfgError::UnexpectedPass { .. } | PostCfgError::MissingPass(_) => (
            source_span,
            "post-CFG effect pass order is incomplete or inconsistent",
        ),
        PostCfgError::InvalidPendingEffect(span) => {
            (span, "post-CFG pending effect identity is inconsistent")
        }
        PostCfgError::PendingEffectLeak(error) => (
            match error {
                DraftSealError::PendingEffect { source_span, .. } => source_span,
                DraftSealError::MissingTerminator(_) => source_span,
            },
            "post-CFG pending effect reached canonical VIR sealing",
        ),
        PostCfgError::LoanEndPlanning(_) => (
            source_span,
            "post-CFG loan-end planning could not prove a safe deterministic placement",
        ),
    };
    FrontendFailure::elaboration(diagnostic_span, message)
}

#[allow(clippy::too_many_arguments)]
fn run_passes(
    function: crate::VirFunctionId,
    memory: &VirMemorySchema,
    mut blocks: Vec<DraftBlock>,
    region_constraints: &[DraftRegionConstraint],
    source_map_entries: &mut [crate::vir::VirSourceMapEntry],
    schedule: &[PostCfgPass],
    source_span: ByteSpan,
    abi: Option<&crate::VirAbiSignature>,
) -> Result<Vec<VirBasicBlock>, PostCfgError> {
    let mut ledger = PassLedger::new();
    let mut sealed = None;
    for pass in schedule {
        ledger.enter(*pass)?;
        match pass {
            PostCfgPass::InitializationEffects => {
                validate_pending_identities(&blocks)?;
                assignment::plan_initialization_effects(memory, &mut blocks, source_span, abi)
                    .map_err(PostCfgError::InitializationPlanning)?;
            }
            PostCfgPass::LoanEndEffects => {
                loan_end::plan(
                    function,
                    region_constraints,
                    &mut blocks,
                    source_map_entries,
                )
                .map_err(PostCfgError::LoanEndPlanning)?;
                materialize_loan_ends(&mut blocks)?;
            }
            PostCfgPass::Seal => {
                sealed = Some(
                    seal_blocks(std::mem::take(&mut blocks))
                        .map_err(PostCfgError::PendingEffectLeak)?,
                );
            }
        }
    }
    ledger.finish()?;
    sealed.ok_or(PostCfgError::MissingPass(PostCfgPass::Seal))
}

fn validate_pending_identities(blocks: &[DraftBlock]) -> Result<(), PostCfgError> {
    for effect in blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction {
            DraftInstruction::Canonical(_) => None,
            DraftInstruction::Pending(effect) => Some(effect),
        })
    {
        if !effect.has_consistent_identity() {
            return Err(PostCfgError::InvalidPendingEffect(
                effect.identity().source_span,
            ));
        }
    }
    Ok(())
}

fn materialize_loan_ends(blocks: &mut [DraftBlock]) -> Result<(), PostCfgError> {
    for block in blocks {
        for instruction in &mut block.instructions {
            let DraftInstruction::Pending(effect) = instruction else {
                continue;
            };
            if !matches!(effect, PendingEffect::LoanEnd(_)) {
                continue;
            }
            if !effect.has_consistent_identity() {
                return Err(PostCfgError::InvalidPendingEffect(
                    effect.identity().source_span,
                ));
            }
            let canonical =
                effect
                    .determined_instruction()
                    .ok_or(PostCfgError::InvalidPendingEffect(
                        effect.identity().source_span,
                    ))?;
            *instruction = DraftInstruction::Canonical(Box::new(canonical));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{POST_CFG_PASSES, PostCfgError, PostCfgPass, run_passes};
    use crate::ByteSpan;
    use crate::frontend::hir::HirNodeId;
    use crate::frontend::lower::draft::{
        DraftBlock, DraftEffectIdentity, DraftInstruction, DraftObjectIdentity,
        DraftSourceIdentity, PendingAssignment, PendingAssignmentSource, PendingEffect,
        seal_blocks,
    };
    use crate::vir::{
        SpannedVirTerminator, VirBlockId, VirMemoryAccess, VirMemorySchema, VirTerminator,
        VirValueId,
    };

    fn span() -> ByteSpan {
        ByteSpan::new(0, 10).expect("ordered span")
    }

    #[test]
    fn planning_diagnostic_preserves_kind_and_assignment_span() {
        let failure = crate::frontend::FrontendFailure::unsupported(
            ByteSpan::new(4, 7).unwrap(),
            "initialization state is unknown",
        );
        assert_eq!(
            super::pass_failure(
                PostCfgError::InitializationPlanning(failure.clone()),
                span()
            ),
            failure
        );
    }

    fn empty_block() -> DraftBlock {
        DraftBlock {
            id: VirBlockId::new(0),
            parameters: Vec::new(),
            instructions: Vec::new(),
            terminator: Some(SpannedVirTerminator {
                terminator: VirTerminator::Return { values: Vec::new() },
                source_span: span(),
            }),
            source_span: span(),
        }
    }

    #[test]
    fn pass_order_is_total_and_cannot_be_omitted_or_repeated() {
        let memory = VirMemorySchema::core_u64();
        let mut source_map = Vec::new();
        let missing = run_passes(
            crate::VirFunctionId::new(0),
            &memory,
            vec![empty_block()],
            &[],
            &mut source_map,
            &POST_CFG_PASSES[..1],
            span(),
            None,
        );
        assert_eq!(
            missing,
            Err(PostCfgError::MissingPass(PostCfgPass::LoanEndEffects))
        );

        let repeated = run_passes(
            crate::VirFunctionId::new(0),
            &memory,
            vec![empty_block()],
            &[],
            &mut source_map,
            &[
                PostCfgPass::InitializationEffects,
                PostCfgPass::InitializationEffects,
            ],
            span(),
            None,
        );
        assert_eq!(
            repeated,
            Err(PostCfgError::UnexpectedPass {
                expected: Some(PostCfgPass::LoanEndEffects),
                found: PostCfgPass::InitializationEffects,
            })
        );

        assert!(
            run_passes(
                crate::VirFunctionId::new(0),
                &memory,
                vec![empty_block()],
                &[],
                &mut source_map,
                POST_CFG_PASSES,
                span(),
                None,
            )
            .is_ok()
        );
    }

    #[test]
    fn pending_effects_and_identity_mutations_fail_before_canonical_vir() {
        let access = VirMemoryAccess::core_u64();
        let identity = DraftEffectIdentity {
            source: DraftSourceIdentity::HirNode(HirNodeId::new(0)),
            object: DraftObjectIdentity {
                pointer: VirValueId::new(0),
                permission: VirValueId::new(1),
                access,
            },
            source_span: span(),
        };
        let mut block = empty_block();
        block
            .instructions
            .push(DraftInstruction::Pending(PendingEffect::Assignment(
                PendingAssignment {
                    identity,
                    destination: VirValueId::new(9),
                    destination_permission: VirValueId::new(1),
                    access,
                    source: PendingAssignmentSource::Scalar {
                        value: VirValueId::new(2),
                    },
                    source_span: span(),
                },
            )));
        assert!(matches!(
            run_passes(
                crate::VirFunctionId::new(0),
                &VirMemorySchema::core_u64(),
                vec![block.clone()],
                &[],
                &mut Vec::new(),
                POST_CFG_PASSES,
                span(),
                None,
            ),
            Err(PostCfgError::InvalidPendingEffect(_))
        ));
        assert!(seal_blocks(vec![block]).is_err());
    }
}
