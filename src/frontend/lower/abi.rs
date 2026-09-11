//! Signature classification, entry/result ABI binding and slot mapping.
//! Methods operate on the one Lowerer and emit the same private Draft effects.
use super::{
    AbiCallStorageRole, ByteSpan, ConcreteTypes, DraftSourceIdentity, FrontendFailure,
    HirExpression, HirExpressionKind, HirLocalId, HirProgram, HirTypeKind, LoweredLoan,
    LoweredMemorySchema, LoweredObject, LoweredValue, Lowerer, PendingAssignmentSource,
    VirAbiSignature, VirAbiValue, VirInstruction, VirLoanKind, VirTerminator, VirType, VirValue,
    VirValueId, concrete, invalid_hir, lowered_value_ids, object_source_mode, runtime_value,
};

pub(super) fn classify_hir_signature(
    types: ConcreteTypes<'_>,
    memory: &LoweredMemorySchema,
    signature: &crate::frontend::hir::HirFunctionSignature,
    source_span: ByteSpan,
) -> Result<VirAbiSignature, FrontendFailure> {
    let signature_access = |ty| {
        let access = types.abi_access(memory, ty, source_span)?;
        if let Some(
            crate::VirMemoryTypeKind::Pointer {
                pointee,
                kind: crate::VirPointerKind::Reference,
                ..
            }
            | crate::VirMemoryTypeKind::Slice {
                element: pointee, ..
            },
        ) = memory.schema().kind(access.ty)
        {
            let pointee = memory
                .schema()
                .access(*pointee)
                .ok_or_else(|| invalid_hir(source_span))?;
            let shape = memory
                .schema()
                .object_shape(pointee)
                .map_err(|_| invalid_hir(source_span))?;
            if !shape.resource_leaves().is_empty()
                || !shape.variants().is_empty()
                || shape.size_bytes() > concrete::HIR_AGGREGATE_MAX_BYTES
            {
                return Err(FrontendFailure::unsupported(
                    source_span,
                    "borrowed interface referents require a bounded pointer-free layout without active variants",
                ));
            }
        }
        Ok(access)
    };
    let parameters = signature
        .parameters
        .iter()
        .map(|ty| signature_access(*ty))
        .collect::<Result<Vec<_>, _>>()?;
    let result = signature_access(signature.return_type)?;
    VirAbiSignature::classify_with_borrow_results_validated(
        memory.schema(),
        &parameters,
        &[result],
        signature.borrow_result,
        signature.borrow_result_alternatives.clone(),
    )
    .map_err(|_| invalid_hir(source_span))
}

pub(super) fn hir_parameter_abi_slot(
    hir: &HirProgram,
    memory: &LoweredMemorySchema,
    function: crate::frontend::hir::HirFunctionId,
    local: HirLocalId,
    source_span: ByteSpan,
) -> Result<u32, FrontendFailure> {
    let function = hir
        .function_by_id(function)
        .ok_or_else(|| invalid_hir(source_span))?;
    let body = function.body().ok_or_else(|| invalid_hir(source_span))?;
    let parameter = body
        .parameters
        .iter()
        .position(|candidate| *candidate == local)
        .ok_or_else(|| invalid_hir(source_span))?;
    let abi = classify_hir_signature(
        ConcreteTypes::new(hir),
        memory,
        &function.signature,
        source_span,
    )?;
    abi.parameters()
        .get(parameter)
        .and_then(|binding| binding.parameter_slots().first())
        .copied()
        .ok_or_else(|| invalid_hir(source_span))
}

impl Lowerer<'_> {
    pub(super) fn bind_abi_entry_parameters(
        &mut self,
        body: &crate::frontend::hir::HirBody,
        physical: &[VirValue],
    ) -> Result<(), FrontendFailure> {
        let bindings = self.abi.parameters().to_vec();
        for ((local, source_ty), binding) in body
            .parameters
            .iter()
            .zip(&self.function.signature.parameters)
            .zip(&bindings)
        {
            match binding.value() {
                VirAbiValue::Unit { .. } => {}
                VirAbiValue::Scalar { ty, .. } => {
                    let [slot] = binding.parameter_slots() else {
                        return Err(invalid_hir(self.function.span));
                    };
                    let value = self.abi_parameter(physical, *slot, *ty)?;
                    if self.storage_locals.contains(local) {
                        let destination = self.local_object(*local, self.function.span)?;
                        self.cfg.emit_assignment(
                            destination.pointer,
                            destination.permission,
                            destination.access,
                            PendingAssignmentSource::Scalar { value: value.id },
                            DraftSourceIdentity::FunctionEntry(self.function.id),
                            self.function.span,
                        )?;
                    } else {
                        self.environment.initialize(
                            *local,
                            runtime_value(value),
                            self.function.span,
                        )?;
                    }
                }
                VirAbiValue::Pointer { pointee, .. } => {
                    let [pointer_slot, permission_slot] = binding.parameter_slots() else {
                        return Err(invalid_hir(self.function.span));
                    };
                    let pointer = self.abi_parameter(
                        physical,
                        *pointer_slot,
                        VirType::Pointer { access: *pointee },
                    )?;
                    let permission =
                        self.abi_parameter(physical, *permission_slot, VirType::Permission)?;
                    let drop_flag = self.initial_drop_flag(*source_ty, true, self.function.span)?;
                    self.environment.initialize(
                        *local,
                        LoweredValue {
                            value: pointer.id,
                            ty: pointer.ty,
                            metadata: None,
                            permission: Some(permission.id),
                            drop_flag,
                            loan: if binding.interface().transfer.is_borrow() {
                                Some(LoweredLoan::Authority {
                                    kind: if binding.interface().transfer
                                        == crate::VirInterfaceTransfer::BorrowShared
                                    {
                                        VirLoanKind::Shared
                                    } else {
                                        VirLoanKind::Mutable
                                    },
                                    reference: binding
                                        .value()
                                        .access()
                                        .ok_or_else(|| invalid_hir(self.function.span))?,
                                })
                            } else {
                                None
                            },
                        },
                        self.function.span,
                    )?;
                    if let [slot] = binding.result_slots() {
                        self.abi_parameter_restores.push((*slot, *local));
                    }
                }
                VirAbiValue::Slice { element, .. } => {
                    let [pointer_slot, length_slot, permission_slot] = binding.parameter_slots()
                    else {
                        return Err(invalid_hir(self.function.span));
                    };
                    let pointer = self.abi_parameter(
                        physical,
                        *pointer_slot,
                        VirType::Pointer { access: *element },
                    )?;
                    let length = self.abi_parameter(physical, *length_slot, VirType::U64)?;
                    let permission =
                        self.abi_parameter(physical, *permission_slot, VirType::Permission)?;
                    self.environment.initialize(
                        *local,
                        LoweredValue {
                            value: pointer.id,
                            ty: pointer.ty,
                            metadata: Some(length.id),
                            permission: Some(permission.id),
                            drop_flag: None,
                            loan: matches!(
                                self.hir.type_kind(*source_ty),
                                Some(HirTypeKind::Reference { .. })
                            )
                            .then_some(LoweredLoan::Authority {
                                kind: if binding.interface().transfer
                                    == crate::VirInterfaceTransfer::BorrowShared
                                {
                                    VirLoanKind::Shared
                                } else {
                                    VirLoanKind::Mutable
                                },
                                reference: binding
                                    .value()
                                    .access()
                                    .ok_or_else(|| invalid_hir(self.function.span))?,
                            }),
                        },
                        self.function.span,
                    )?;
                    if let [result_slot] = binding.result_slots() {
                        self.abi_parameter_restores.push((*result_slot, *local));
                    }
                }
                VirAbiValue::DirectAggregate { access, leaves } => {
                    if self.memory.access(*source_ty, self.function.span)? != *access {
                        return Err(invalid_hir(self.function.span));
                    }
                    let destination = self.local_object(*local, self.function.span)?;
                    let values = binding
                        .parameter_slots()
                        .iter()
                        .zip(leaves)
                        .map(|(slot, leaf)| self.abi_parameter(physical, *slot, leaf.ty()))
                        .collect::<Result<Vec<_>, _>>()?;
                    self.initialize_abi_leaves(destination, leaves, &values, self.function.span)?;
                }
                VirAbiValue::IndirectAggregate { access } => {
                    let [pointer_slot, permission_slot] = binding.parameter_slots() else {
                        return Err(invalid_hir(self.function.span));
                    };
                    let pointer = self.abi_parameter(
                        physical,
                        *pointer_slot,
                        VirType::Pointer { access: *access },
                    )?;
                    let permission =
                        self.abi_parameter(physical, *permission_slot, VirType::Permission)?;
                    let drop_flag = self.initial_drop_flag(*source_ty, true, self.function.span)?;
                    self.environment.initialize(
                        *local,
                        LoweredValue {
                            value: pointer.id,
                            ty: pointer.ty,
                            metadata: None,
                            permission: Some(permission.id),
                            drop_flag,
                            loan: None,
                        },
                        self.function.span,
                    )?;
                    let [result_slot] = binding.result_slots() else {
                        return Err(invalid_hir(self.function.span));
                    };
                    self.abi_parameter_restores.push((*result_slot, *local));
                }
                VirAbiValue::Opaque(_) => {
                    return Err(invalid_hir(self.function.span));
                }
            }
        }

        if let Some(binding) = self.abi.results().first()
            && let VirAbiValue::IndirectAggregate { access } = binding.value()
        {
            let [pointer_slot, permission_slot] = binding.parameter_slots() else {
                return Err(invalid_hir(self.function.span));
            };
            let pointer = self.abi_parameter(
                physical,
                *pointer_slot,
                VirType::Pointer { access: *access },
            )?;
            let permission = self.abi_parameter(physical, *permission_slot, VirType::Permission)?;
            let local = self
                .abi_indirect_result
                .ok_or_else(|| invalid_hir(self.function.span))?;
            self.environment.initialize(
                local,
                LoweredValue {
                    value: pointer.id,
                    ty: VirType::Pointer { access: *access },
                    metadata: None,
                    permission: Some(permission.id),
                    drop_flag: None,
                    loan: None,
                },
                self.function.span,
            )?;
        }
        Ok(())
    }

    pub(super) fn abi_parameter(
        &self,
        physical: &[VirValue],
        slot: u32,
        expected: VirType,
    ) -> Result<VirValue, FrontendFailure> {
        physical
            .get(slot as usize)
            .copied()
            .filter(|value| value.ty == expected)
            .ok_or_else(|| invalid_hir(self.function.span))
    }

    pub(super) fn initialize_abi_leaves(
        &mut self,
        destination: LoweredObject,
        leaves: &[crate::VirAbiLeaf],
        values: &[VirValue],
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        if leaves.len() != values.len() {
            return Err(invalid_hir(source_span));
        }
        for (leaf, value) in leaves.iter().zip(values) {
            let pointer = self.fresh_value(
                VirType::Pointer {
                    access: leaf.access(),
                },
                source_span,
            )?;
            self.emit(
                VirInstruction::ObjectLeafAddress {
                    result: pointer,
                    base: destination.pointer,
                    owner: destination.access,
                    leaf: leaf.access(),
                    offset_bytes: leaf.offset_bytes(),
                },
                source_span,
            )?;
            self.emit(
                VirInstruction::Initialize {
                    pointer: pointer.id,
                    value: value.id,
                    permission: destination.permission,
                    access: leaf.access(),
                },
                source_span,
            )?;
        }
        Ok(())
    }

    pub(super) fn load_abi_leaves(
        &mut self,
        source: LoweredObject,
        leaves: &[crate::VirAbiLeaf],
        source_span: ByteSpan,
    ) -> Result<Vec<VirValue>, FrontendFailure> {
        let mut values = Vec::with_capacity(leaves.len());
        for leaf in leaves {
            let pointer = self.fresh_value(
                VirType::Pointer {
                    access: leaf.access(),
                },
                source_span,
            )?;
            self.emit(
                VirInstruction::ObjectLeafAddress {
                    result: pointer,
                    base: source.pointer,
                    owner: source.access,
                    leaf: leaf.access(),
                    offset_bytes: leaf.offset_bytes(),
                },
                source_span,
            )?;
            let value = self.fresh_value(leaf.ty(), source_span)?;
            self.emit(
                VirInstruction::Load {
                    result: value,
                    pointer: pointer.id,
                    permission: source.permission,
                    access: leaf.access(),
                },
                source_span,
            )?;
            values.push(value);
        }
        Ok(values)
    }

    pub(super) fn lower_return(
        &mut self,
        value: Option<&HirExpression>,
        source_span: ByteSpan,
    ) -> Result<(), FrontendFailure> {
        let return_type = self.function.signature.return_type;
        match value {
            Some(value)
                if value.ty == return_type
                    || (self.hir.reference_compatible(value.ty, return_type)
                        && (!self.abi.borrow_result_alternatives().is_empty()
                            || self.abi.borrow_result().is_some())) => {}
            None if self.hir.type_kind(return_type) == Some(&HirTypeKind::Unit) => {}
            _ => return Err(invalid_hir(source_span)),
        }
        let binding = self
            .abi
            .results()
            .first()
            .cloned()
            .ok_or_else(|| invalid_hir(source_span))?;
        let mut results = vec![None; self.abi.physical().results.len()];
        match binding.value() {
            VirAbiValue::Unit { .. } => {
                self.types.require_unit_layout(return_type, source_span)?;
                if value.is_some_and(|value| !matches!(value.kind, HirExpressionKind::Unit)) {
                    return Err(invalid_hir(source_span));
                }
            }
            VirAbiValue::Scalar { .. } => {
                let value =
                    self.lower_expression(value.ok_or_else(|| invalid_hir(source_span))?)?;
                require_pointer_abi_authority(value, source_span)?;
                assign_abi_slots(
                    &mut results,
                    binding.result_slots(),
                    &lowered_value_ids(value),
                    source_span,
                )?;
            }
            VirAbiValue::Pointer { .. } => {
                let expression = value.ok_or_else(|| invalid_hir(source_span))?;
                let lowered = self.lower_expression(expression)?;
                require_pointer_abi_authority(lowered, source_span)?;
                let lowered =
                    self.conditional_mutable_return(expression, lowered, &binding, source_span)?;
                assign_abi_slots(
                    &mut results,
                    binding.result_slots(),
                    &lowered_value_ids(lowered),
                    source_span,
                )?;
            }
            VirAbiValue::DirectAggregate { leaves, .. } => {
                let value = value.ok_or_else(|| invalid_hir(source_span))?;
                let source = self.lower_object_expression(value)?;
                let values = self.load_abi_leaves(source, leaves, source_span)?;
                let ids = values.iter().map(|value| value.id).collect::<Vec<_>>();
                assign_abi_slots(&mut results, binding.result_slots(), &ids, source_span)?;
                self.cleanup_object_temporary(
                    source,
                    DraftSourceIdentity::HirNode(value.id),
                    source_span,
                )?;
            }
            VirAbiValue::IndirectAggregate { access } => {
                let value = value.ok_or_else(|| invalid_hir(source_span))?;
                let source_mode = object_source_mode(value)?;
                let source = self.lower_object_expression(value)?;
                let destination = self.storage_object(
                    self.abi_indirect_result
                        .ok_or_else(|| invalid_hir(source_span))?,
                    source_span,
                )?;
                if source.access != *access || destination.access != *access {
                    return Err(invalid_hir(source_span));
                }
                self.emit(
                    VirInstruction::ObjectTransfer {
                        destination: destination.pointer,
                        destination_permission: destination.permission,
                        source: source.pointer,
                        source_permission: source.permission,
                        access: *access,
                        destination_mode: crate::VirObjectDestinationMode::Initialize,
                        source_mode,
                    },
                    source_span,
                )?;
                if source_mode == crate::VirObjectSourceMode::Move && source.drop_flag.is_some() {
                    self.set_object_drop_flag(source, false, source_span)?;
                }
                let [permission_slot] = binding.result_slots() else {
                    return Err(invalid_hir(source_span));
                };
                assign_abi_slots(
                    &mut results,
                    &[*permission_slot],
                    &[destination.permission],
                    source_span,
                )?;
                if source_mode == crate::VirObjectSourceMode::Copy {
                    self.cleanup_object_temporary(
                        source,
                        DraftSourceIdentity::HirNode(value.id),
                        source_span,
                    )?;
                }
            }
            VirAbiValue::Slice { .. } => {
                let expression = value.ok_or_else(|| invalid_hir(source_span))?;
                let lowered = self.lower_expression(expression)?;
                let lowered =
                    self.conditional_mutable_return(expression, lowered, &binding, source_span)?;
                assign_abi_slots(
                    &mut results,
                    binding.result_slots(),
                    &lowered_value_ids(lowered),
                    source_span,
                )?;
            }
            VirAbiValue::Opaque(_) => return Err(invalid_hir(source_span)),
        }
        let mut exported = Vec::new();
        for (slot, parameter) in &self.abi_parameter_restores {
            let local = if self.environment.optional(*parameter).is_some() {
                *parameter
            } else {
                // A mutable reference may have moved to another local. Its
                // parameter-owned HIR region identifies the return endpoint;
                // VIR still independently checks the actual loan authority.
                let ty = self.local(*parameter, source_span)?.ty;
                let body = self
                    .function
                    .body()
                    .ok_or_else(|| invalid_hir(source_span))?;
                let candidates = body
                    .locals
                    .iter()
                    .filter(|local| {
                        local.ty == ty
                            && self
                                .environment
                                .optional(local.id)
                                .is_some_and(|value| value.loan.is_some())
                    })
                    .map(|local| local.id)
                    .collect::<Vec<_>>();
                let [local] = candidates.as_slice() else {
                    return Err(invalid_hir(source_span));
                };
                *local
            };
            let permission = self
                .lookup_local(local, source_span)?
                .permission
                .ok_or_else(|| invalid_hir(source_span))?;
            assign_abi_slots(&mut results, &[*slot], &[permission], source_span)?;
            if self
                .environment
                .optional(local)
                .is_some_and(|value| value.loan.is_some())
            {
                exported.push(local);
            }
        }
        let values = results
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| invalid_hir(source_span))?;
        self.environment.forget(&exported, source_span)?;
        self.terminate_scope_exit(None, VirTerminator::Return { values }, source_span, false)
    }

    fn conditional_mutable_return(
        &mut self,
        expression: &HirExpression,
        parent: LoweredValue,
        binding: &crate::VirAbiBinding,
        source_span: ByteSpan,
    ) -> Result<LoweredValue, FrontendFailure> {
        if binding.interface().transfer != crate::VirInterfaceTransfer::BorrowMutable {
            return Ok(parent);
        }
        if let Some(relation) = self.abi.borrow_result()
            && relation.projection != crate::BorrowProjection::Whole
        {
            return Ok(parent);
        }
        if self.abi.borrow_result_alternatives().is_empty() {
            return Ok(parent);
        }
        let parameter_index = self
            .function
            .signature
            .parameters
            .iter()
            .enumerate()
            .find(|(index, ty)| {
                **ty == expression.ty && self.abi.borrow_result_parameters().contains(index)
            })
            .map(|(index, _)| index)
            .ok_or_else(|| invalid_hir(source_span))?;
        let local = *self
            .function
            .body()
            .and_then(|body| body.parameters.get(parameter_index))
            .ok_or_else(|| invalid_hir(source_span))?;
        let permission = parent.permission.ok_or_else(|| invalid_hir(source_span))?;
        let reference = binding
            .value()
            .access()
            .ok_or_else(|| invalid_hir(source_span))?;
        let region = match self.hir.type_kind(self.function.signature.return_type) {
            Some(HirTypeKind::Reference { region, .. }) => *region,
            _ => return Err(invalid_hir(source_span)),
        };
        let loan = crate::VirLoanId::new(self.next_loan);
        self.next_loan = self
            .next_loan
            .checked_add(1)
            .ok_or_else(|| invalid_hir(source_span))?;
        let reference_result = self.fresh_value(parent.ty, source_span)?;
        let permission_result = self.fresh_value(VirType::Permission, source_span)?;
        self.emit_generated(
            VirInstruction::LoanReborrowAuthority {
                loan,
                region: super::vir_borrow_region_id(self.hir, region)
                    .ok_or_else(|| invalid_hir(source_span))?,
                effect: super::loan_authority_effect(parent.value, permission, reference),
                reference_result,
                permission_result,
            },
            source_span,
            crate::VirGeneratedReason::LoanEffect,
        )?;
        self.environment.initialize(local, parent, source_span)?;
        Ok(LoweredValue {
            value: reference_result.id,
            ty: reference_result.ty,
            metadata: parent.metadata,
            permission: Some(permission_result.id),
            drop_flag: None,
            loan: Some(LoweredLoan::Authority {
                kind: VirLoanKind::Mutable,
                reference,
            }),
        })
    }

    pub(super) fn abi_call_storage_object(
        &self,
        expression: &HirExpression,
        role: AbiCallStorageRole,
        source_span: ByteSpan,
    ) -> Result<(HirLocalId, LoweredObject), FrontendFailure> {
        let local = self
            .abi_call_storage
            .iter()
            .find(|candidate| candidate.owner == expression.id && candidate.role == role)
            .map(|candidate| candidate.local)
            .ok_or_else(|| invalid_hir(source_span))?;
        Ok((local, self.storage_object(local, source_span)?))
    }
}

pub(super) fn require_pointer_abi_authority(
    value: LoweredValue,
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    if matches!(value.ty, VirType::Pointer { .. }) && value.permission.is_none() {
        return Err(FrontendFailure::unsupported(
            source_span,
            "authority-free raw address call/return ABI remains gated: legacy pointer ABI requires authority; stage 7.5.7 covers supported carriers only",
        ));
    }
    Ok(())
}

pub(super) fn assign_abi_slots(
    output: &mut [Option<VirValueId>],
    slots: &[u32],
    values: &[VirValueId],
    source_span: ByteSpan,
) -> Result<(), FrontendFailure> {
    if slots.len() != values.len() {
        return Err(invalid_hir(source_span));
    }
    for (slot, value) in slots.iter().zip(values) {
        let destination = output
            .get_mut(*slot as usize)
            .filter(|destination| destination.is_none())
            .ok_or_else(|| invalid_hir(source_span))?;
        *destination = Some(*value);
    }
    Ok(())
}

pub(super) fn abi_result(
    results: &[VirValue],
    slot: u32,
    expected: VirType,
    source_span: ByteSpan,
) -> Result<VirValue, FrontendFailure> {
    results
        .get(slot as usize)
        .copied()
        .filter(|value| value.ty == expected)
        .ok_or_else(|| invalid_hir(source_span))
}
