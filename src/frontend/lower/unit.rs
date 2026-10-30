//! Function/unit boundary between private draft lowering and canonical VIR.

use super::draft::{DraftFunctionBody, DraftRegionConstraint};
use crate::ByteSpan;
use crate::vir::{
    VirBasicBlock, VirBlockId, VirContractId, VirFunction, VirFunctionAbi, VirFunctionId,
    VirSourceMapEntry,
};

/// Function header plus private draft body. No public API can observe it.
#[derive(Clone)]
pub(super) struct DraftLoweredFunction {
    pub(super) loop_specs: Vec<super::loop_spec::LoopSpec>,
    pub(super) local_specs: Vec<super::local_spec::LocalSpec>,
    pub(super) id: VirFunctionId,
    pub(super) name: String,
    pub(super) signature: crate::VirSignature,
    pub(super) contract: VirContractId,
    pub(super) entry: VirBlockId,
    pub(super) body: DraftFunctionBody,
    pub(super) region_constraints: Vec<DraftRegionConstraint>,
    pub(super) abi: crate::VirAbiSignature,
    pub(super) source_span: ByteSpan,
}

/// Only post-CFG sealing can construct this canonical producer result.
#[derive(Clone)]
pub(super) struct CanonicalLoweredFunction {
    pub(super) loop_specs: Vec<super::loop_spec::LoopSpec>,
    pub(super) local_specs: Vec<super::local_spec::LocalSpec>,
    pub(super) function: VirFunction,
    pub(super) abi: VirFunctionAbi,
    pub(super) source_map_entries: Vec<VirSourceMapEntry>,
}

pub(super) fn seal_function(
    draft: DraftLoweredFunction,
    mut blocks: Vec<VirBasicBlock>,
) -> CanonicalLoweredFunction {
    canonicalize_loan_ids(&mut blocks);
    CanonicalLoweredFunction {
        loop_specs: draft.loop_specs,
        local_specs: draft.local_specs,
        abi: VirFunctionAbi {
            function: draft.id,
            signature: draft.abi,
        },
        function: VirFunction {
            id: draft.id,
            name: draft.name,
            signature: draft.signature,
            contract: draft.contract,
            entry: draft.entry,
            blocks,
            source_span: draft.source_span,
        },
        source_map_entries: draft.body.source_map_entries,
    }
}

/// Block creation order can differ from lowering order (notably a loop in
/// one branch followed by a borrow in the other). Loan IDs belong to the
/// final instruction stream, after pending ends have been materialized.
fn canonicalize_loan_ids(blocks: &mut [VirBasicBlock]) {
    use crate::{VirInstruction as I, VirLoanId};
    let mut ids = std::collections::BTreeMap::new();
    for block in blocks.iter() {
        for instruction in &block.instructions {
            let old = match instruction.instruction {
                I::LoanBegin { effect, .. } | I::LoanReborrow { effect, .. } => effect.loan,
                I::LoanReborrowAuthority { loan, .. } => loan,
                _ => continue,
            };
            let next = VirLoanId::new(ids.len() as u32);
            // Duplicate declarations remain invalid; do not silently repair them.
            ids.entry(old).or_insert(next);
        }
    }
    for block in blocks {
        for instruction in &mut block.instructions {
            match &mut instruction.instruction {
                I::LoanBegin { effect, .. }
                | I::LoanReborrow { effect, .. }
                | I::LoanAliasShared { effect, .. }
                | I::LoanEnd { effect } => {
                    if let Some(id) = ids.get(&effect.loan) {
                        effect.loan = *id;
                    }
                    if let Some(parent) = effect.parent.as_mut()
                        && let Some(id) = ids.get(parent)
                    {
                        *parent = *id;
                    }
                }
                I::LoanReborrowAuthority { loan, .. } => {
                    if let Some(id) = ids.get(loan) {
                        *loan = *id;
                    }
                }
                _ => {}
            }
        }
    }
}
