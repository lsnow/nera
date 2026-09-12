//! Deterministic VIR CFG construction and lexical-environment transfer.

#[cfg(test)]
use super::cleanup::ScopeExitPlan;
use super::draft::{
    DraftBlock, DraftEffectIdentity, DraftFunctionBody, DraftInstruction, DraftObjectIdentity,
    DraftSourceIdentity, PendingAssignment, PendingAssignmentSource, PendingCleanup,
    PendingCleanupKind, PendingEffect, PendingLoanEnd, PendingLoanEndEffect,
};
use super::invalid_hir;
use crate::ByteSpan;
use crate::diagnostic::span_contains;
use crate::frontend::FrontendFailure;
use crate::frontend::hir::{HirLocalId, HirScopeId};
use crate::vir::{
    SpannedVirInstruction, SpannedVirTerminator, VirBlockId, VirBlockTarget, VirBorrowRegionId,
    VirFunctionId, VirGeneratedReason, VirInstruction, VirLoanEffect, VirLoanId, VirLoanKind,
    VirLoanRange, VirLocation, VirMemoryAccess, VirSourceMapEntry, VirTerminator, VirType,
    VirValue, VirValueId,
};

const ENTRY_BLOCK: VirBlockId = VirBlockId::new(0);

/// A runtime local and its optional authority. Own/reference values carry a
/// linear permission across CFG edges; address-only raw values carry none.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct LoweredValue {
    pub(super) value: VirValueId,
    pub(super) ty: VirType,
    pub(super) metadata: Option<VirValueId>,
    pub(super) permission: Option<VirValueId>,
    pub(super) drop_flag: Option<VirValueId>,
    pub(super) loan: Option<LoweredLoan>,
}

/// Loan metadata attached to the changing pointer/permission SSA pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LoweredLoan {
    /// A reference produced directly by a canonical loan site.
    Static(LoweredLoanMetadata),
    /// A reference moved out of an aggregate payload. Its permission carries
    /// the path-sensitive loan identity, so lowering must not guess one.
    Authority {
        kind: VirLoanKind,
        reference: VirMemoryAccess,
    },
    /// A conditional mutable or projected call result. Temporary argument
    /// loans cannot end until the selected child ends; bounded candidates are
    /// closed in source order immediately afterwards.
    ConditionalAuthority {
        kind: VirLoanKind,
        reference: VirMemoryAccess,
        deferred: [Option<DeferredLoanEnd>; 4],
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DeferredLoanEnd {
    Static {
        loan: LoweredLoanMetadata,
        pointer: VirValueId,
        permission: VirValueId,
    },
    Authority {
        reference: VirMemoryAccess,
        pointer: VirValueId,
        permission: VirValueId,
    },
}

impl LoweredLoan {
    pub(super) const fn kind(self) -> VirLoanKind {
        match self {
            Self::Static(metadata) => metadata.kind,
            Self::Authority { kind, .. } | Self::ConditionalAuthority { kind, .. } => kind,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct LoweredLoanMetadata {
    pub(super) id: VirLoanId,
    pub(super) kind: VirLoanKind,
    pub(super) region: VirBorrowRegionId,
    pub(super) parent: Option<VirLoanId>,
    pub(super) reference: VirMemoryAccess,
    pub(super) range: VirLoanRange,
}

impl LoweredValue {
    fn has_valid_resource_shape(self) -> bool {
        (self.permission.is_none() || matches!(self.ty, VirType::Pointer { .. }))
            && (self.metadata.is_none() || self.permission.is_some())
            && (self.drop_flag.is_none() || self.permission.is_some())
            && (self.loan.is_none()
                || (matches!(self.ty, VirType::Pointer { .. })
                    && self.permission.is_some()
                    && self.drop_flag.is_none()))
            && self.ty != VirType::Permission
    }
}

/// Function-local environment indexed by dense `HirLocalId`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LocalEnvironment {
    values: Vec<Option<LoweredValue>>,
}

impl LocalEnvironment {
    pub(super) fn new(local_count: usize) -> Self {
        Self {
            values: vec![None; local_count],
        }
    }

    pub(super) fn lookup(
        &self,
        local: HirLocalId,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        self.values
            .get(local.index())
            .copied()
            .flatten()
            .filter(|value| value.has_valid_resource_shape())
            .ok_or_else(|| invalid_hir(source_span))
    }

    pub(super) fn initialize(
        &mut self,
        local: HirLocalId,
        value: LoweredValue,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if !value.has_valid_resource_shape() {
            return Err(invalid_hir(source_span));
        }
        let slot = self
            .values
            .get_mut(local.index())
            .ok_or_else(|| invalid_hir(source_span))?;
        if slot.is_some() {
            return Err(invalid_hir(source_span));
        }
        *slot = Some(value);
        Ok(())
    }

    pub(super) fn reassign(
        &mut self,
        local: HirLocalId,
        value: LoweredValue,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if !value.has_valid_resource_shape() {
            return Err(invalid_hir(source_span));
        }
        let slot = self
            .values
            .get_mut(local.index())
            .ok_or_else(|| invalid_hir(source_span))?;
        if slot.is_none() {
            return Err(invalid_hir(source_span));
        }
        *slot = Some(value);
        Ok(())
    }

    pub(super) fn len(&self) -> usize {
        self.values.len()
    }

    pub(super) fn optional(&self, local: HirLocalId) -> Option<LoweredValue> {
        self.values.get(local.index()).copied().flatten()
    }

    pub(super) fn require_uninitialized(
        &self,
        locals: &[HirLocalId],
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if locals
            .iter()
            .all(|local| self.values.get(local.index()).is_some_and(Option::is_none))
        {
            Ok(())
        } else {
            Err(invalid_hir(source_span))
        }
    }

    pub(super) fn forget(
        &mut self,
        locals: &[HirLocalId],
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        for local in locals {
            let slot = self
                .values
                .get_mut(local.index())
                .ok_or_else(|| invalid_hir(source_span))?;
            *slot = None;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct EnvironmentBinding {
    local: HirLocalId,
    value: VirValue,
    metadata: Option<VirValue>,
    permission: Option<VirValue>,
    drop_flag: Option<VirValue>,
    loan: Option<LoweredLoan>,
}

/// A block whose parameters reconstruct the common initialized environment of
/// all incoming edges. Binding and argument order is local-ID order, followed
/// by metadata, permission and drop flag when those components exist.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct EnvironmentBlock {
    block: VirBlockId,
    scope: HirScopeId,
    bindings: Vec<EnvironmentBinding>,
    extra_parameters: Vec<VirValue>,
    local_count: usize,
}

impl EnvironmentBlock {
    pub(super) const fn block(&self) -> VirBlockId {
        self.block
    }

    pub(super) const fn scope(&self) -> HirScopeId {
        self.scope
    }

    pub(super) fn extra_parameters(&self) -> &[VirValue] {
        &self.extra_parameters
    }

    pub(super) fn contains_local(&self, local: HirLocalId) -> bool {
        self.bindings.iter().any(|binding| binding.local == local)
    }

    pub(super) fn entry_environment(&self) -> LocalEnvironment {
        let mut environment = LocalEnvironment::new(self.local_count);
        for binding in &self.bindings {
            environment.values[binding.local.index()] = Some(LoweredValue {
                value: binding.value.id,
                ty: binding.value.ty,
                metadata: binding.metadata.map(|metadata| metadata.id),
                permission: binding.permission.map(|permission| permission.id),
                drop_flag: binding.drop_flag.map(|flag| flag.id),
                loan: binding.loan,
            });
        }
        environment
    }

    pub(super) fn target_from_with_extras(
        &self,
        environment: &LocalEnvironment,
        extras: &[VirValue],
        source_span: ByteSpan,
    ) -> Result<VirBlockTarget, FrontendFailure> {
        if environment.len() != self.local_count {
            return Err(invalid_hir(source_span));
        }
        let mut arguments = Vec::with_capacity(
            self.bindings.len()
                + self
                    .bindings
                    .iter()
                    .filter(|binding| binding.metadata.is_some())
                    .count()
                + self
                    .bindings
                    .iter()
                    .filter(|binding| binding.permission.is_some())
                    .count()
                + self
                    .bindings
                    .iter()
                    .filter(|binding| binding.drop_flag.is_some())
                    .count()
                + extras.len(),
        );
        for binding in &self.bindings {
            let source = environment.lookup(binding.local, source_span)?;
            if source.ty != binding.value.ty
                || source.metadata.is_some() != binding.metadata.is_some()
                || source.permission.is_some() != binding.permission.is_some()
                || source.drop_flag.is_some() != binding.drop_flag.is_some()
                || source.loan != binding.loan
            {
                return Err(invalid_hir(source_span));
            }
            arguments.push(source.value);
            if let Some(metadata) = source.metadata {
                arguments.push(metadata);
            }
            if let Some(permission) = source.permission {
                arguments.push(permission);
            }
            if let Some(drop_flag) = source.drop_flag {
                arguments.push(drop_flag);
            }
        }
        if extras.len() != self.extra_parameters.len()
            || extras
                .iter()
                .zip(&self.extra_parameters)
                .any(|(argument, parameter)| argument.ty != parameter.ty)
        {
            return Err(invalid_hir(source_span));
        }
        arguments.extend(extras.iter().map(|value| value.id));
        Ok(VirBlockTarget {
            block: self.block,
            arguments,
        })
    }
}

/// The only constructor for VIR blocks used by HIR lowering.
pub(super) struct CfgBuilder {
    function: VirFunctionId,
    blocks: Vec<DraftBlock>,
    current: Option<VirBlockId>,
    next_value: u32,
    function_span: ByteSpan,
    source_map_entries: Vec<VirSourceMapEntry>,
}

impl CfgBuilder {
    #[cfg(test)]
    pub(super) fn new(
        root_scope: HirScopeId,
        local_count: usize,
        entry_span: ByteSpan,
    ) -> Result<(Self, EnvironmentBlock), FrontendFailure> {
        Self::new_with_parameters(
            VirFunctionId::new(0),
            root_scope,
            local_count,
            &[],
            entry_span,
        )
    }

    /// Creates the function entry block and binds source parameter locals to
    /// its VIR parameters. Pointer parameters receive an adjacent permission.
    #[cfg(test)]
    pub(super) fn new_with_parameters(
        function: VirFunctionId,
        root_scope: HirScopeId,
        local_count: usize,
        parameters: &[(HirLocalId, VirType)],
        entry_span: ByteSpan,
    ) -> Result<(Self, EnvironmentBlock), FrontendFailure> {
        let parameter_locals = parameters
            .iter()
            .map(|(local, _)| *local)
            .collect::<Vec<_>>();
        if !strictly_increasing(&parameter_locals)
            || parameters
                .iter()
                .any(|(local, ty)| local.index() >= local_count || *ty == VirType::Permission)
        {
            return Err(invalid_hir(entry_span));
        }
        let mut builder = Self {
            function,
            blocks: Vec::new(),
            current: None,
            next_value: 0,
            function_span: entry_span,
            source_map_entries: vec![VirSourceMapEntry::user(
                VirLocation::FunctionEntry { function },
                entry_span,
            )],
        };
        let block = builder.create_block(entry_span)?;
        let mut bindings = Vec::with_capacity(parameters.len());
        for (local, ty) in parameters {
            let value = builder.fresh_value(*ty, entry_span)?;
            builder.push_parameter(block, value, None, entry_span)?;
            let permission = if matches!(ty, VirType::Pointer { .. }) {
                let permission = builder.fresh_value(VirType::Permission, entry_span)?;
                builder.push_parameter(
                    block,
                    permission,
                    Some(VirGeneratedReason::PermissionParameter),
                    entry_span,
                )?;
                Some(permission)
            } else {
                None
            };
            bindings.push(EnvironmentBinding {
                local: *local,
                value,
                metadata: None,
                permission,
                drop_flag: None,
                loan: None,
            });
        }
        let entry = EnvironmentBlock {
            block,
            scope: root_scope,
            bindings,
            extra_parameters: Vec::new(),
            local_count,
        };
        if entry.block() != ENTRY_BLOCK {
            return Err(invalid_hir(entry_span));
        }
        builder.switch_to(entry.block(), entry_span)?;
        Ok((builder, entry))
    }

    /// Creates an entry block from an already classified physical ABI. The
    /// caller reconstructs logical locals from the returned SSA parameters.
    pub(super) fn new_with_abi_parameters(
        function: VirFunctionId,
        root_scope: HirScopeId,
        local_count: usize,
        parameter_types: &[VirType],
        entry_span: ByteSpan,
    ) -> Result<(Self, EnvironmentBlock, Vec<VirValue>), FrontendFailure> {
        let mut builder = Self {
            function,
            blocks: Vec::new(),
            current: None,
            next_value: 0,
            function_span: entry_span,
            source_map_entries: vec![VirSourceMapEntry::user(
                VirLocation::FunctionEntry { function },
                entry_span,
            )],
        };
        let block = builder.create_block(entry_span)?;
        let mut physical = Vec::with_capacity(parameter_types.len());
        for ty in parameter_types {
            let value = builder.fresh_value(*ty, entry_span)?;
            let reason =
                (*ty == VirType::Permission).then_some(VirGeneratedReason::PermissionParameter);
            builder.push_parameter(block, value, reason, entry_span)?;
            physical.push(value);
        }
        let entry = EnvironmentBlock {
            block,
            scope: root_scope,
            bindings: Vec::new(),
            extra_parameters: Vec::new(),
            local_count,
        };
        if entry.block() != ENTRY_BLOCK {
            return Err(invalid_hir(entry_span));
        }
        builder.switch_to(entry.block(), entry_span)?;
        Ok((builder, entry, physical))
    }

    pub(super) const fn entry(&self) -> VirBlockId {
        ENTRY_BLOCK
    }

    pub(super) fn has_open_block(&self) -> bool {
        self.current.is_some()
    }

    pub(super) fn open_block_covers(&self, span: ByteSpan) -> bool {
        self.current
            .and_then(|id| self.blocks.get(id.get() as usize))
            .is_some_and(|block| span_contains(block.source_span, span))
    }

    pub(super) fn create_block(
        &mut self,
        source_span: ByteSpan,
    ) -> Result<VirBlockId, FrontendFailure> {
        if !span_contains(self.function_span, source_span) {
            return Err(invalid_hir(source_span));
        }
        let raw = u32::try_from(self.blocks.len())
            .map_err(|_| FrontendFailure::elaboration(source_span, "too many VIR basic blocks"))?;
        let id = VirBlockId::new(raw);
        let location = VirLocation::BlockEntry {
            function: self.function,
            block: id,
        };
        let origin = if self.blocks.is_empty() {
            VirSourceMapEntry::user(location, source_span)
        } else {
            VirSourceMapEntry::generated(
                location,
                source_span,
                VirGeneratedReason::ControlFlowBlock,
            )
        };
        self.blocks.push(DraftBlock {
            id,
            parameters: Vec::new(),
            instructions: Vec::new(),
            terminator: None,
            source_span,
        });
        self.source_map_entries.push(origin);
        Ok(id)
    }

    /// Creates a target block from locals initialized on every predecessor.
    /// `visible_locals` must be in declaration/ID order for deterministic ABI.
    #[cfg(test)]
    pub(super) fn create_environment_block(
        &mut self,
        scope: HirScopeId,
        visible_locals: &[HirLocalId],
        predecessors: &[&LocalEnvironment],
        source_span: ByteSpan,
    ) -> Result<EnvironmentBlock, FrontendFailure> {
        self.create_environment_block_with_extras(
            scope,
            visible_locals,
            predecessors,
            &[],
            source_span,
        )
    }

    pub(super) fn create_environment_block_with_extras(
        &mut self,
        scope: HirScopeId,
        visible_locals: &[HirLocalId],
        predecessors: &[&LocalEnvironment],
        extra_types: &[VirType],
        source_span: ByteSpan,
    ) -> Result<EnvironmentBlock, FrontendFailure> {
        let local_count = predecessors
            .first()
            .map_or(0, |environment| environment.len());
        if predecessors
            .iter()
            .any(|environment| environment.len() != local_count)
            || !strictly_increasing(visible_locals)
            || visible_locals
                .iter()
                .any(|local| local.index() >= local_count)
            || extra_types
                .iter()
                .any(|ty| !matches!(ty, VirType::U64 | VirType::Bool))
        {
            return Err(invalid_hir(source_span));
        }

        let mut common_values = Vec::new();
        for local in visible_locals {
            let values: Option<Vec<_>> = predecessors
                .iter()
                .map(|environment| environment.optional(*local))
                .collect();
            let Some(values) = values else {
                continue;
            };
            let Some(first) = values.first().copied() else {
                continue;
            };
            if !first.has_valid_resource_shape()
                || values.iter().any(|value| {
                    !value.has_valid_resource_shape()
                        || value.ty != first.ty
                        || value.metadata.is_some() != first.metadata.is_some()
                        || value.permission.is_some() != first.permission.is_some()
                        || value.drop_flag.is_some() != first.drop_flag.is_some()
                })
            {
                return Err(invalid_hir(source_span));
            }

            common_values.push((*local, first));
        }

        let parameter_count = common_values.len()
            + common_values
                .iter()
                .filter(|(_, value)| value.metadata.is_some())
                .count()
            + common_values
                .iter()
                .filter(|(_, value)| value.permission.is_some())
                .count()
            + common_values
                .iter()
                .filter(|(_, value)| value.drop_flag.is_some())
                .count()
            + extra_types.len();
        let parameter_count = u32::try_from(parameter_count)
            .map_err(|_| FrontendFailure::elaboration(source_span, "too many VIR values"))?;
        self.next_value
            .checked_add(parameter_count)
            .ok_or_else(|| FrontendFailure::elaboration(source_span, "too many VIR values"))?;

        // Validation is complete before block/value allocation, so ordinary
        // malformed-environment failures do not leave a partial CFG behind.
        let block = self.create_block(source_span)?;
        let mut bindings = Vec::with_capacity(common_values.len());
        for (local, first) in common_values {
            let value = self.fresh_value(first.ty, source_span)?;
            self.push_parameter(
                block,
                value,
                Some(VirGeneratedReason::BlockParameter),
                source_span,
            )?;
            let metadata = if first.metadata.is_some() {
                let metadata = self.fresh_value(VirType::U64, source_span)?;
                self.push_parameter(
                    block,
                    metadata,
                    Some(VirGeneratedReason::BlockParameter),
                    source_span,
                )?;
                Some(metadata)
            } else {
                None
            };
            let permission = if first.permission.is_some() {
                let permission = self.fresh_value(VirType::Permission, source_span)?;
                self.push_parameter(
                    block,
                    permission,
                    Some(VirGeneratedReason::BlockParameter),
                    source_span,
                )?;
                Some(permission)
            } else {
                None
            };
            let drop_flag = if first.drop_flag.is_some() {
                let flag = self.fresh_value(VirType::Bool, source_span)?;
                self.push_parameter(
                    block,
                    flag,
                    Some(VirGeneratedReason::BlockParameter),
                    source_span,
                )?;
                Some(flag)
            } else {
                None
            };
            bindings.push(EnvironmentBinding {
                local,
                value,
                metadata,
                permission,
                drop_flag,
                loan: first.loan,
            });
        }
        let mut extra_parameters = Vec::with_capacity(extra_types.len());
        for ty in extra_types {
            let parameter = self.fresh_value(*ty, source_span)?;
            self.push_parameter(
                block,
                parameter,
                Some(VirGeneratedReason::BlockParameter),
                source_span,
            )?;
            extra_parameters.push(parameter);
        }
        let environment_block = EnvironmentBlock {
            block,
            scope,
            bindings,
            extra_parameters,
            local_count,
        };
        for predecessor in predecessors {
            environment_block.target_from_with_extras(
                predecessor,
                &environment_block.extra_parameters,
                source_span,
            )?;
        }
        Ok(environment_block)
    }

    pub(super) fn switch_to(
        &mut self,
        block: VirBlockId,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if self.current.is_some() {
            return Err(invalid_hir(source_span));
        }
        let target = self.block_mut(block, source_span)?;
        if target.terminator.is_some() {
            return Err(invalid_hir(source_span));
        }
        self.current = Some(block);
        Ok(())
    }

    pub(super) fn fresh_value(
        &mut self,
        ty: VirType,
        source_span: ByteSpan,
    ) -> Result<VirValue, FrontendFailure> {
        let id = VirValueId::new(self.next_value);
        self.next_value = self
            .next_value
            .checked_add(1)
            .ok_or_else(|| FrontendFailure::elaboration(source_span, "too many VIR values"))?;
        Ok(VirValue { id, ty })
    }

    pub(super) fn emit(
        &mut self,
        instruction: VirInstruction,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        self.emit_with_origin(instruction, source_span, None)
    }

    pub(super) fn emit_generated(
        &mut self,
        instruction: VirInstruction,
        parent_span: ByteSpan,
        reason: VirGeneratedReason,
    ) -> Result<(), FrontendFailure> {
        self.emit_with_origin(instruction, parent_span, Some(reason))
    }

    fn emit_with_origin(
        &mut self,
        instruction: VirInstruction,
        source_span: ByteSpan,
        generated: Option<VirGeneratedReason>,
    ) -> Result<(), FrontendFailure> {
        let block = self.current.ok_or_else(|| invalid_hir(source_span))?;
        let current = self.block_mut(block, source_span)?;
        if current.terminator.is_some() || !span_contains(current.source_span, source_span) {
            return Err(invalid_hir(source_span));
        }
        let ordinal = u64::try_from(current.instructions.len())
            .map_err(|_| FrontendFailure::elaboration(source_span, "too many VIR instructions"))?;
        let is_call = matches!(instruction, VirInstruction::Call { .. });
        current
            .instructions
            .push(DraftInstruction::Canonical(Box::new(
                SpannedVirInstruction {
                    instruction,
                    source_span,
                },
            )));
        let instruction_location = VirLocation::Instruction {
            function: self.function,
            block,
            ordinal,
        };
        self.source_map_entries.push(generated.map_or_else(
            || VirSourceMapEntry::user(instruction_location, source_span),
            |reason| VirSourceMapEntry::generated(instruction_location, source_span, reason),
        ));
        if is_call {
            let call_edge = VirLocation::CallEdge {
                function: self.function,
                block,
                instruction: ordinal,
            };
            self.source_map_entries.push(generated.map_or_else(
                || VirSourceMapEntry::user(call_edge, source_span),
                |reason| VirSourceMapEntry::generated(call_edge, source_span, reason),
            ));
        }
        Ok(())
    }

    pub(super) fn emit_assignment(
        &mut self,
        destination: VirValueId,
        destination_permission: VirValueId,
        access: VirMemoryAccess,
        source: PendingAssignmentSource,
        source_identity: DraftSourceIdentity,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        self.emit_pending(
            PendingEffect::Assignment(PendingAssignment {
                identity: DraftEffectIdentity {
                    source: source_identity,
                    object: DraftObjectIdentity {
                        pointer: destination,
                        permission: destination_permission,
                        access,
                    },
                    source_span,
                },
                destination,
                destination_permission,
                access,
                source,
                source_span,
            }),
            None,
        )
    }

    pub(super) fn emit_cleanup(
        &mut self,
        kind: PendingCleanupKind,
        object: DraftObjectIdentity,
        source: DraftSourceIdentity,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let generated = matches!(
            kind,
            PendingCleanupKind::OwnedAllocation { .. }
                | PendingCleanupKind::Object { condition: Some(_) }
        )
        .then_some(VirGeneratedReason::ImplicitDrop);
        self.emit_pending(
            PendingEffect::Cleanup(PendingCleanup {
                identity: DraftEffectIdentity {
                    source,
                    object,
                    source_span,
                },
                kind,
            }),
            generated,
        )
    }

    pub(super) fn emit_loan_end(
        &mut self,
        effect: VirLoanEffect,
        source: DraftSourceIdentity,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let object = DraftObjectIdentity {
            pointer: effect.source_pointer,
            permission: effect.source_permission,
            access: effect.reference,
        };
        self.emit_pending(
            PendingEffect::LoanEnd(PendingLoanEnd {
                identity: DraftEffectIdentity {
                    source,
                    object,
                    source_span,
                },
                effect: PendingLoanEndEffect::Static(effect),
            }),
            Some(VirGeneratedReason::LoanEffect),
        )
    }

    pub(super) fn emit_loan_authority_end(
        &mut self,
        effect: crate::VirLoanAuthorityEffect,
        source: DraftSourceIdentity,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let object = DraftObjectIdentity {
            pointer: effect.source_pointer,
            permission: effect.source_permission,
            access: effect.reference,
        };
        self.emit_pending(
            PendingEffect::LoanEnd(PendingLoanEnd {
                identity: DraftEffectIdentity {
                    source,
                    object,
                    source_span,
                },
                effect: PendingLoanEndEffect::Authority(effect),
            }),
            Some(VirGeneratedReason::LoanEffect),
        )
    }

    fn emit_pending(
        &mut self,
        effect: PendingEffect,
        generated: Option<VirGeneratedReason>,
    ) -> Result<(), FrontendFailure> {
        let source_span = effect.identity().source_span;
        if !effect.has_consistent_identity() {
            return Err(invalid_hir(source_span));
        }
        let block = self.current.ok_or_else(|| invalid_hir(source_span))?;
        let current = self.block_mut(block, source_span)?;
        if current.terminator.is_some() || !span_contains(current.source_span, source_span) {
            return Err(invalid_hir(source_span));
        }
        let ordinal = u64::try_from(current.instructions.len())
            .map_err(|_| FrontendFailure::elaboration(source_span, "too many VIR instructions"))?;
        current.instructions.push(DraftInstruction::Pending(effect));
        let location = VirLocation::Instruction {
            function: self.function,
            block,
            ordinal,
        };
        self.source_map_entries.push(generated.map_or_else(
            || VirSourceMapEntry::user(location, source_span),
            |reason| VirSourceMapEntry::generated(location, source_span, reason),
        ));
        Ok(())
    }

    pub(super) fn terminate(
        &mut self,
        terminator: VirTerminator,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        self.terminate_with_origin(terminator, source_span, None)
    }

    pub(super) fn terminate_generated(
        &mut self,
        terminator: VirTerminator,
        parent_span: ByteSpan,
        reason: VirGeneratedReason,
    ) -> Result<(), FrontendFailure> {
        self.terminate_with_origin(terminator, parent_span, Some(reason))
    }

    fn terminate_with_origin(
        &mut self,
        terminator: VirTerminator,
        source_span: ByteSpan,
        generated: Option<VirGeneratedReason>,
    ) -> Result<(), FrontendFailure> {
        let block = self.current.ok_or_else(|| invalid_hir(source_span))?;
        let current = self.block_mut(block, source_span)?;
        if current.terminator.is_some() || !span_contains(current.source_span, source_span) {
            return Err(invalid_hir(source_span));
        }
        current.terminator = Some(SpannedVirTerminator {
            terminator,
            source_span,
        });
        let location = VirLocation::Terminator {
            function: self.function,
            block,
        };
        self.source_map_entries.push(generated.map_or_else(
            || VirSourceMapEntry::user(location, source_span),
            |reason| VirSourceMapEntry::generated(location, source_span, reason),
        ));
        self.current = None;
        Ok(())
    }

    pub(super) fn finish_draft(
        self,
        source_span: ByteSpan,
    ) -> Result<DraftFunctionBody, FrontendFailure> {
        if self.current.is_some()
            || self.blocks.is_empty()
            || self.blocks.iter().any(|block| block.terminator.is_none())
        {
            return Err(invalid_hir(source_span));
        }
        Ok(DraftFunctionBody {
            blocks: self.blocks,
            source_map_entries: self.source_map_entries,
        })
    }

    #[cfg(test)]
    pub(super) fn finish(
        self,
        source_span: ByteSpan,
    ) -> Result<(Vec<crate::VirBasicBlock>, Vec<VirSourceMapEntry>), FrontendFailure> {
        let body = self.finish_draft(source_span)?;
        super::post_cfg::canonicalize_body_for_test(
            &crate::VirMemorySchema::core_u64(),
            body,
            source_span,
        )
    }

    fn push_parameter(
        &mut self,
        block: VirBlockId,
        parameter: VirValue,
        generated: Option<VirGeneratedReason>,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let parameters = &mut self.block_mut(block, source_span)?.parameters;
        let ordinal = u64::try_from(parameters.len())
            .map_err(|_| FrontendFailure::elaboration(source_span, "too many VIR parameters"))?;
        parameters.push(parameter);
        let location = VirLocation::BlockParameter {
            function: self.function,
            block,
            ordinal,
        };
        self.source_map_entries.push(generated.map_or_else(
            || VirSourceMapEntry::user(location, source_span),
            |reason| VirSourceMapEntry::generated(location, source_span, reason),
        ));
        Ok(())
    }

    fn block_mut(
        &mut self,
        block: VirBlockId,
        source_span: ByteSpan,
    ) -> Result<&mut DraftBlock, FrontendFailure> {
        self.blocks
            .get_mut(block.get() as usize)
            .filter(|candidate| candidate.id == block)
            .ok_or_else(|| invalid_hir(source_span))
    }
}

/// Common exit boundary for fallthrough, return, break and continue. Jump
/// callers first obtain their `VirBlockTarget` from `EnvironmentBlock`.
#[cfg(test)]
pub(super) fn terminate_scope_exit(
    builder: &mut CfgBuilder,
    active_scopes: &[HirScopeId],
    retained_scope: Option<HirScopeId>,
    terminator: VirTerminator,
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    emit_scope_exit_actions(builder, active_scopes, retained_scope, source_span)?;
    builder.terminate(terminator, source_span)
}

/// Emits the cleanup portion of a lexical fallthrough without forcing a CFG
/// edge. Core0 has no actions yet, but every exit kind validates one scope plan.
#[cfg(test)]
pub(super) fn emit_scope_exit_actions(
    _builder: &mut CfgBuilder,
    active_scopes: &[HirScopeId],
    retained_scope: Option<HirScopeId>,
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    let _cleanup_order = ScopeExitPlan::new(active_scopes, retained_scope, source_span)?;
    // There are deliberately no implicit destructor/free actions in Core0.
    // The validated order becomes actionable when the language defines cleanup.
    Ok(())
}

fn strictly_increasing(locals: &[HirLocalId]) -> bool {
    locals.windows(2).all(|pair| pair[0] < pair[1])
}

#[cfg(test)]
mod tests {
    use super::{CfgBuilder, LocalEnvironment, LoweredValue, ScopeExitPlan, terminate_scope_exit};
    use crate::ByteSpan;
    use crate::frontend::hir::{HirLocalId, HirScopeId};
    use crate::vir::{
        VirBlockId, VirConstant, VirContractId, VirFunction, VirFunctionId, VirInstruction,
        VirMemoryAccess, VirMemorySchema, VirRegionId, VirSignature, VirTerminator, VirType,
        VirUnit, VirValueId,
    };

    fn span() -> ByteSpan {
        ByteSpan::new(0, 100).expect("ordered span")
    }

    fn builder() -> CfgBuilder {
        CfgBuilder::new(HirScopeId::new(0), 3, span())
            .expect("entry CFG")
            .0
    }

    fn scalar(id: u32) -> LoweredValue {
        LoweredValue {
            value: VirValueId::new(id),
            ty: VirType::U64,
            metadata: None,
            permission: None,
            drop_flag: None,
            loan: None,
        }
    }

    fn pointer(value: u32, permission: u32) -> LoweredValue {
        LoweredValue {
            value: VirValueId::new(value),
            ty: VirType::Pointer {
                access: VirMemoryAccess::core_u64(),
            },
            metadata: None,
            permission: Some(VirValueId::new(permission)),
            drop_flag: None,
            loan: None,
        }
    }

    #[test]
    fn environment_join_is_deterministic_and_keeps_pointer_permission_pairs() {
        let mut malformed = LocalEnvironment::new(1);
        assert!(
            malformed
                .initialize(
                    HirLocalId::new(0),
                    LoweredValue {
                        value: VirValueId::new(0),
                        ty: VirType::Pointer {
                            access: VirMemoryAccess::core_u64(),
                        },
                        metadata: Some(VirValueId::new(1)),
                        permission: None,
                        drop_flag: None,
                        loan: None,
                    },
                    span(),
                )
                .is_err()
        );

        let mut left = LocalEnvironment::new(3);
        left.initialize(HirLocalId::new(0), scalar(10), span())
            .expect("left scalar");
        left.initialize(HirLocalId::new(1), pointer(11, 12), span())
            .expect("left pointer");
        left.initialize(HirLocalId::new(2), scalar(13), span())
            .expect("left-only scalar");
        let mut right = LocalEnvironment::new(3);
        right
            .initialize(HirLocalId::new(0), scalar(20), span())
            .expect("right scalar");
        right
            .initialize(HirLocalId::new(1), pointer(21, 22), span())
            .expect("right pointer");

        let mut builder = builder();
        let join = builder
            .create_environment_block(
                HirScopeId::new(0),
                &[HirLocalId::new(0), HirLocalId::new(1), HirLocalId::new(2)],
                &[&left, &right],
                span(),
            )
            .expect("common environment");
        assert_eq!(join.block(), VirBlockId::new(1));
        assert_eq!(join.scope(), HirScopeId::new(0));
        assert_eq!(
            join.target_from_with_extras(&left, &[], span())
                .expect("left edge")
                .arguments,
            [
                VirValueId::new(10),
                VirValueId::new(11),
                VirValueId::new(12)
            ]
        );
        assert_eq!(
            join.target_from_with_extras(&right, &[], span())
                .expect("right edge")
                .arguments,
            [
                VirValueId::new(20),
                VirValueId::new(21),
                VirValueId::new(22)
            ]
        );
        let joined = join.entry_environment();
        assert!(joined.lookup(HirLocalId::new(0), span()).is_ok());
        assert!(joined.lookup(HirLocalId::new(1), span()).is_ok());
        assert!(joined.lookup(HirLocalId::new(2), span()).is_err());
    }

    #[test]
    fn environment_update_failure_does_not_replace_the_previous_value() {
        let mut environment = LocalEnvironment::new(1);
        environment
            .initialize(HirLocalId::new(0), scalar(7), span())
            .expect("first initialization");
        assert!(
            environment
                .initialize(HirLocalId::new(0), scalar(8), span())
                .is_err()
        );
        assert_eq!(
            environment
                .lookup(HirLocalId::new(0), span())
                .expect("original binding remains"),
            scalar(7)
        );
    }

    #[test]
    fn malformed_environment_block_does_not_consume_a_block_id() {
        let root_scope = HirScopeId::new(0);
        let (mut builder, entry) = CfgBuilder::new(root_scope, 2, span()).expect("entry CFG");
        let environment = entry.entry_environment();
        assert!(
            builder
                .create_environment_block(
                    root_scope,
                    &[HirLocalId::new(1), HirLocalId::new(0)],
                    &[&environment],
                    span(),
                )
                .is_err()
        );
        let outside = ByteSpan::new(101, 102).expect("ordered outside span");
        assert!(builder.create_block(outside).is_err());
        assert_eq!(
            builder.create_block(span()).expect("first non-entry block"),
            VirBlockId::new(1)
        );
    }

    #[test]
    fn builder_rejects_incomplete_blocks_and_duplicate_termination() {
        let mut unfinished = builder();
        unfinished.create_block(span()).expect("second block");
        unfinished
            .terminate(VirTerminator::Return { values: Vec::new() }, span())
            .expect("entry return");
        assert!(unfinished.finish(span()).is_err());

        let mut duplicate = builder();
        duplicate
            .terminate(VirTerminator::Return { values: Vec::new() }, span())
            .expect("first terminator");
        assert!(
            duplicate
                .terminate(VirTerminator::Return { values: Vec::new() }, span())
                .is_err()
        );

        let mut invalid_span = builder();
        let outside = ByteSpan::new(101, 102).expect("ordered outside span");
        assert!(
            invalid_span
                .terminate(VirTerminator::Return { values: Vec::new() }, outside)
                .is_err()
        );
        invalid_span
            .terminate(VirTerminator::Return { values: Vec::new() }, span())
            .expect("failed termination preserves the active block");
        invalid_span.finish(span()).expect("complete CFG");
    }

    #[test]
    fn scope_exit_order_is_inner_to_outer_and_empty_cleanup_stays_direct() {
        let active = [HirScopeId::new(0), HirScopeId::new(1), HirScopeId::new(2)];
        assert_eq!(
            ScopeExitPlan::new(&active, Some(HirScopeId::new(0)), span())
                .expect("break-like exit")
                .leaving_scopes(),
            [HirScopeId::new(2), HirScopeId::new(1)]
        );
        assert_eq!(
            ScopeExitPlan::new(&active, None, span())
                .expect("return exit")
                .leaving_scopes(),
            [HirScopeId::new(2), HirScopeId::new(1), HirScopeId::new(0)]
        );
        assert!(ScopeExitPlan::new(&active, Some(HirScopeId::new(9)), span()).is_err());
        assert!(
            ScopeExitPlan::new(
                &[HirScopeId::new(0), HirScopeId::new(1), HirScopeId::new(1)],
                None,
                span(),
            )
            .is_err()
        );

        let mut builder = builder();
        terminate_scope_exit(
            &mut builder,
            &active,
            None,
            VirTerminator::Return { values: Vec::new() },
            span(),
        )
        .expect("empty cleanup plan terminates directly");
        let (blocks, _) = builder.finish(span()).expect("complete CFG");
        assert_eq!(blocks.len(), 1);
        assert!(matches!(
            blocks[0].terminator.terminator,
            VirTerminator::Return { .. }
        ));
    }

    #[test]
    fn environment_edge_builds_validator_accepted_cfg() {
        let root_scope = HirScopeId::new(0);
        let (mut builder, entry) = CfgBuilder::new(root_scope, 2, span()).expect("entry CFG");
        let size = builder
            .fresh_value(VirType::U64, span())
            .expect("size value");
        builder
            .emit(
                VirInstruction::Constant {
                    result: size,
                    value: VirConstant::U64(8),
                },
                span(),
            )
            .expect("size instruction");
        let scalar_value = builder
            .fresh_value(VirType::U64, span())
            .expect("scalar value");
        builder
            .emit(
                VirInstruction::Constant {
                    result: scalar_value,
                    value: VirConstant::U64(42),
                },
                span(),
            )
            .expect("scalar instruction");
        let pointer_type = VirType::Pointer {
            access: VirMemoryAccess::core_u64(),
        };
        let pointer_value = builder
            .fresh_value(pointer_type, span())
            .expect("pointer value");
        let permission_value = builder
            .fresh_value(VirType::Permission, span())
            .expect("permission value");
        builder
            .emit(
                VirInstruction::Allocate {
                    pointer_result: pointer_value,
                    permission_result: permission_value,
                    size_bytes: size.id,
                    alignment: 8,
                    region: VirRegionId::new(0),
                    element: VirMemoryAccess::core_u64(),
                },
                span(),
            )
            .expect("allocation instruction");

        let mut environment = entry.entry_environment();
        environment
            .initialize(HirLocalId::new(0), scalar(scalar_value.id.get()), span())
            .expect("scalar local");
        environment
            .initialize(
                HirLocalId::new(1),
                pointer(pointer_value.id.get(), permission_value.id.get()),
                span(),
            )
            .expect("pointer local");
        let target = builder
            .create_environment_block(
                root_scope,
                &[HirLocalId::new(0), HirLocalId::new(1)],
                &[&environment],
                span(),
            )
            .expect("join block");
        let edge = target
            .target_from_with_extras(&environment, &[], span())
            .expect("environment edge");
        terminate_scope_exit(
            &mut builder,
            &[root_scope],
            Some(root_scope),
            VirTerminator::Jump { target: edge },
            span(),
        )
        .expect("jump through scope-exit boundary");
        builder
            .switch_to(target.block(), span())
            .expect("enter join block");
        let joined = target.entry_environment();
        let joined_pointer = joined
            .lookup(HirLocalId::new(1), span())
            .expect("joined pointer");
        builder
            .emit(
                VirInstruction::Free {
                    pointer: joined_pointer.value,
                    permission: joined_pointer.permission.expect("paired permission"),
                },
                span(),
            )
            .expect("free joined pointer");
        let joined_scalar = joined
            .lookup(HirLocalId::new(0), span())
            .expect("joined scalar");
        terminate_scope_exit(
            &mut builder,
            &[root_scope],
            None,
            VirTerminator::Return {
                values: vec![joined_scalar.value],
            },
            span(),
        )
        .expect("return through scope-exit boundary");

        let program = VirUnit::from_runtime(
            VirMemorySchema::core_u64(),
            VirFunctionId::new(0),
            vec![VirFunction {
                id: VirFunctionId::new(0),
                name: "cfg-builder".to_owned(),
                signature: VirSignature {
                    parameters: Vec::new(),
                    results: vec![VirType::U64],
                },
                contract: VirContractId::new(0),
                entry: builder.entry(),
                blocks: builder.finish(span()).expect("finished CFG").0,
                source_span: span(),
            }],
        );
        program.validate().expect("builder emits valid SSA CFG");
    }
}
