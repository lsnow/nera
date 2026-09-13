//! Private snapshots and instruction boundaries; never runtime instructions.
use super::*;
use crate::VirBlockId;

#[derive(Clone)]
pub(super) struct LocalSpec {
    pub prove: crate::HirSpecProveId,
    pub function: VirFunctionId,
    pub block: VirBlockId,
    pub boundary: usize,
    pub values: BTreeMap<HirLocalId, cfg::LoweredValue>,
}

impl LocalSpec {
    pub fn pointer(
        &self,
        snapshot: HirSpecSnapshot,
        authority: bool,
        span: ByteSpan,
    ) -> Result<VirSpecSnapshot, FrontendFailure> {
        let HirSpecSnapshot::Local { function, local } = snapshot else {
            return Err(invalid_hir(span));
        };
        if function.get() != self.function.get() {
            return Err(invalid_hir(span));
        }
        let value = self
            .values
            .get(&local)
            .filter(|v| matches!(v.ty, VirType::Pointer { .. }))
            .ok_or_else(|| {
                FrontendFailure::unsupported(
                    span,
                    "resource snapshot is not available at this CFG point",
                )
            })?;
        Ok(VirSpecSnapshot::Value {
            function: self.function,
            value: if authority {
                value.permission.ok_or_else(|| invalid_hir(span))?
            } else {
                value.value
            },
        })
    }
    pub fn location(&self) -> VirSpecLocation {
        VirSpecLocation::Runtime(if self.boundary == 0 {
            VirLocation::BlockEntry {
                function: self.function,
                block: self.block,
            }
        } else {
            VirLocation::Instruction {
                function: self.function,
                block: self.block,
                ordinal: (self.boundary - 1) as u64,
            }
        })
    }

    pub fn scalar(
        &self,
        local: HirLocalId,
        ty: VirSpecType,
        span: ByteSpan,
    ) -> Result<VirSpecSnapshot, FrontendFailure> {
        let value = self.values.get(&local).ok_or_else(|| {
            FrontendFailure::unsupported(span, "assert snapshot is not retained at this CFG point")
        })?;
        if !matches!(
            (value.ty, ty),
            (VirType::Bool, VirSpecType::Bool) | (VirType::U64, VirSpecType::U64)
        ) {
            return Err(FrontendFailure::unsupported(
                span,
                "assert cannot read object-backed storage without a supported logical heap-value query",
            ));
        }
        Ok(VirSpecSnapshot::Value {
            function: self.function,
            value: value.value,
        })
    }
}

impl Lowerer<'_> {
    pub(super) fn lower_local_prove(
        &mut self,
        prove: crate::HirSpecProveId,
        span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let (block, boundary) = self.cfg.spec_boundary(span)?;
        let specs = self.hir.specs();
        let clause = specs
            .proves
            .get(prove.index())
            .ok_or_else(|| invalid_hir(span))?
            .clause;
        let snapshots = specs
            .terms
            .iter()
            .filter(|t| t.clause == clause)
            .filter_map(|t| match t.kind {
                HirSpecTermKind::Snapshot(snapshot) => Some(snapshot),
                _ => None,
            })
            .chain(
                specs
                    .assertions
                    .iter()
                    .filter(|a| a.clause == clause)
                    .flat_map(|a| a.kind.snapshots().copied()),
            );
        let used: BTreeSet<_> = snapshots
            .filter_map(|s| match s {
                HirSpecSnapshot::Local { local, .. } => Some(local),
                _ => None,
            })
            .collect();
        let values = used
            .into_iter()
            .filter_map(|local| self.environment.optional(local).map(|value| (local, value)))
            .collect();
        self.local_specs.push(LocalSpec {
            prove,
            function: VirFunctionId::new(self.function.id.get()),
            block,
            boundary,
            values,
        });
        Ok(())
    }
}
