//! Erased loop boundary metadata, finalized against the sealed CFG.
use super::*;
use crate::{VirBlockId, VirLoopBinding, VirLoopBoundary};
mod candidates;
pub(super) use candidates::infer;

#[derive(Clone)]
pub(super) struct LoopSpec {
    pub function: VirFunctionId,
    pub loop_id: HirLoopId,
    pub boundary: VirLoopBoundary,
    pub values: BTreeMap<HirLocalId, cfg::LoweredValue>,
}

pub(super) struct LoopBoundaryPoints {
    pub preheader: VirBlockId,
    pub condition: VirBlockId,
    pub latch: Option<VirBlockId>,
    pub exit: VirBlockId,
}

impl Lowerer<'_> {
    pub(super) fn record_loop_spec(
        &mut self,
        loop_id: HirLoopId,
        header: &EnvironmentBlock,
        points: LoopBoundaryPoints,
        predecessor: &LocalEnvironment,
        for_binding: Option<(HirLocalId, VirValue, VirValue)>,
        carriers: &[VirValue],
    ) {
        let LoopBoundaryPoints {
            preheader,
            condition,
            latch,
            exit,
        } = points;
        let explicit = self
            .hir
            .specs()
            .loop_invariants
            .iter()
            .filter(|i| i.function == self.function.id)
            .collect::<Vec<_>>();
        if !explicit.iter().any(|i| i.loop_id == loop_id)
            && (self.loop_specs.len() >= candidates::MAX_INTERFACES
                || self.cfg.block_count() > candidates::MAX_BLOCKS
                || self.function.body().expect("body").locals.len() > candidates::MAX_LOCALS)
        {
            // Bound discovery metadata too, not only the later search. An
            // omitted real cycle makes the trial fail its independent DAG gate.
            return;
        }
        let head = header.entry_environment();
        let mut bindings = Vec::new();
        for local in &self.function.body().expect("body").locals {
            if let (Some(entry), Some(value)) =
                (predecessor.optional(local.id), head.optional(local.id))
                && matches!(value.ty, VirType::U64 | VirType::Bool)
            {
                bindings.push(VirLoopBinding {
                    local: local.id.get(),
                    entry: entry.value,
                    head: value.value,
                    ty: value.ty,
                });
            } else if !local.mutable
                && let Some(entry) = predecessor.optional(local.id)
                && matches!(entry.ty, VirType::U64 | VirType::Bool)
                && let Some((_, value)) = carriers
                    .iter()
                    .zip(header.extra_parameters())
                    .find(|(source, value)| source.id == entry.value && value.ty == entry.ty)
            {
                // Reuse an already evaluated immutable scalar carrier (notably
                // the for bound). No runtime liveness change or extra evaluation.
                bindings.push(VirLoopBinding {
                    local: local.id.get(),
                    entry: entry.value,
                    head: value.id,
                    ty: value.ty,
                });
            }
        }
        if let Some((local, entry, head)) = for_binding {
            bindings.push(VirLoopBinding {
                local: local.get(),
                entry: entry.id,
                head: head.id,
                ty: head.ty,
            });
        }
        bindings.sort_by_key(|b| b.local);
        self.loop_specs.push(LoopSpec {
            function: VirFunctionId::new(self.function.id.get()),
            loop_id,
            values: self
                .function
                .body()
                .expect("body")
                .locals
                .iter()
                .filter_map(|local| head.optional(local.id).map(|value| (local.id, value)))
                .collect(),
            boundary: VirLoopBoundary {
                loop_id: loop_id.get(),
                preheader,
                header: header.block(),
                condition,
                latch,
                blocks: (header.block().get()..self.cfg.block_count())
                    .map(VirBlockId::new)
                    .filter(|b| *b != exit)
                    .collect(),
                entries: Vec::new(),
                back_edges: Vec::new(),
                exits: Vec::new(),
                bindings,
            },
        });
    }
}
