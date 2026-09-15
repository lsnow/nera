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
    blocks: Vec<VirBasicBlock>,
) -> CanonicalLoweredFunction {
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
