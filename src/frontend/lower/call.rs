//! Signature-driven call lowering and caller-owned ABI temporary storage.

use super::*;

use crate::ByteSpan;
use crate::frontend::hir::{HirLocalId, HirNodeId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AbiCallStorageRole {
    Argument(usize),
    Result,
}

#[derive(Clone, Copy)]
pub(super) struct AbiCallStorage {
    pub(super) owner: HirNodeId,
    pub(super) role: AbiCallStorageRole,
    pub(super) span: ByteSpan,
    pub(super) local: HirLocalId,
}

impl Lowerer<'_> {
    pub(super) fn lower_call(
        &mut self,
        expression: &HirExpression,
        call: &HirCall,
        source_span: ByteSpan,
    ) -> Result<Option<LoweredValue>, FrontendFailure> {
        let callee = self
            .hir
            .function_by_id(call.callee)
            .filter(|callee| {
                callee.signature == call.instantiated_signature
                    && callee.contract == call.contract
                    && callee.signature.calling_convention == call.calling_convention
                    && callee.generic_parameters.is_empty()
                    && callee.body().is_some()
            })
            .ok_or_else(|| invalid_hir(source_span))?;
        if call.arguments.len() != call.instantiated_signature.parameters.len() {
            return Err(invalid_hir(source_span));
        }

        let abi = classify_hir_signature(
            self.types,
            &self.memory,
            &call.instantiated_signature,
            source_span,
        )?;
        let mut arguments = vec![None; abi.physical().parameters.len()];
        let mut restored_arguments = Vec::new();
        let mut restored_slices = Vec::new();
        let mut borrowed_arguments = Vec::new();
        for (index, ((argument, expected), binding)) in call
            .arguments
            .iter()
            .zip(&call.instantiated_signature.parameters)
            .zip(abi.parameters())
            .enumerate()
        {
            if !self.hir.reference_compatible(argument.ty, *expected) {
                return Err(invalid_hir(argument.span));
            }
            if matches!(
                self.hir.type_kind(argument.ty),
                Some(HirTypeKind::Reference { .. })
            ) {
                let returned_source = abi.borrow_result_parameters().contains(&index);
                let local = if binding.interface().transfer
                    == crate::VirInterfaceTransfer::BorrowShared
                    && !returned_source
                {
                    None
                } else {
                    read_resource_local(argument).filter(|_| matches!(&argument.kind, HirExpressionKind::Read { place, .. } if place.projections.is_empty()))
                };
                let value = if let Some(local) = local {
                    self.lookup_local(local, argument.span)?
                } else {
                    self.lower_expression(argument)?
                };
                if value.loan.is_none() {
                    return Err(invalid_hir(argument.span));
                }
                assign_abi_slots(
                    &mut arguments,
                    binding.parameter_slots(),
                    &lowered_value_ids(value),
                    argument.span,
                )?;
                borrowed_arguments.push((
                    index,
                    binding.result_slots().first().copied(),
                    local,
                    value,
                ));
                continue;
            }
            match binding.value() {
                VirAbiValue::Unit { .. } => {
                    if !matches!(argument.kind, HirExpressionKind::Unit) {
                        return Err(invalid_hir(argument.span));
                    }
                }
                VirAbiValue::Scalar { .. } | VirAbiValue::Pointer { .. } => {
                    let value = self.lower_expression(argument)?;
                    require_pointer_abi_authority(value, argument.span)?;
                    assign_abi_slots(
                        &mut arguments,
                        binding.parameter_slots(),
                        &lowered_value_ids(value),
                        argument.span,
                    )?;
                }
                VirAbiValue::Slice { .. } => {
                    let value = self.lower_expression(argument)?;
                    assign_abi_slots(
                        &mut arguments,
                        binding.parameter_slots(),
                        &lowered_value_ids(value),
                        argument.span,
                    )?;
                    let [result_slot] = binding.result_slots() else {
                        return Err(invalid_hir(argument.span));
                    };
                    if let Some(local) = read_resource_local(argument) {
                        restored_slices.push((*result_slot, local));
                    }
                }
                VirAbiValue::DirectAggregate { leaves, .. } => {
                    let source = self.lower_object_expression(argument)?;
                    let values = self.load_abi_leaves(source, leaves, argument.span)?;
                    let ids = values.iter().map(|value| value.id).collect::<Vec<_>>();
                    assign_abi_slots(
                        &mut arguments,
                        binding.parameter_slots(),
                        &ids,
                        argument.span,
                    )?;
                    self.cleanup_object_temporary(
                        source,
                        DraftSourceIdentity::HirNode(argument.id),
                        argument.span,
                    )?;
                }
                VirAbiValue::IndirectAggregate { .. } => {
                    let source = self.lower_object_expression(argument)?;
                    let source_mode = object_source_mode(argument)?;
                    let (local, destination) = self.abi_call_storage_object(
                        expression,
                        AbiCallStorageRole::Argument(index),
                        source_span,
                    )?;
                    self.cfg.emit_assignment(
                        destination.pointer,
                        destination.permission,
                        destination.access,
                        PendingAssignmentSource::Object {
                            pointer: source.pointer,
                            permission: source.permission,
                            mode: source_mode,
                        },
                        DraftSourceIdentity::HirNode(argument.id),
                        argument.span,
                    )?;
                    match source_mode {
                        crate::VirObjectSourceMode::Copy => {
                            self.cleanup_object_temporary(
                                source,
                                DraftSourceIdentity::HirNode(argument.id),
                                argument.span,
                            )?;
                        }
                        crate::VirObjectSourceMode::Move => {
                            if source.drop_flag.is_some() {
                                self.set_object_drop_flag(source, false, argument.span)?;
                            }
                            if destination.drop_flag.is_some() {
                                self.set_object_drop_flag(destination, true, argument.span)?;
                            }
                        }
                    }
                    assign_abi_slots(
                        &mut arguments,
                        binding.parameter_slots(),
                        &[destination.pointer, destination.permission],
                        argument.span,
                    )?;
                    let [result_slot] = binding.result_slots() else {
                        return Err(invalid_hir(argument.span));
                    };
                    restored_arguments.push((
                        *result_slot,
                        local,
                        destination,
                        binding.interface().transfer,
                    ));
                }
                VirAbiValue::Opaque(_) => {
                    return Err(invalid_hir(argument.span));
                }
            }
        }
        let result_binding = abi
            .results()
            .first()
            .ok_or_else(|| invalid_hir(source_span))?;
        let result_storage = match result_binding.value() {
            VirAbiValue::DirectAggregate { .. } | VirAbiValue::IndirectAggregate { .. } => {
                let (_, storage) = self.abi_call_storage_object(
                    expression,
                    AbiCallStorageRole::Result,
                    source_span,
                )?;
                if result_binding.value().is_indirect_aggregate() {
                    assign_abi_slots(
                        &mut arguments,
                        result_binding.parameter_slots(),
                        &[storage.pointer, storage.permission],
                        source_span,
                    )?;
                }
                Some(storage)
            }
            _ => None,
        };
        let arguments = arguments
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| invalid_hir(source_span))?;
        let signature = abi.physical().clone();
        let results = signature
            .results
            .iter()
            .map(|ty| self.fresh_value(*ty, source_span))
            .collect::<Result<Vec<_>, _>>()?;
        self.emit(
            VirInstruction::Call {
                results: results.clone(),
                target: VirCallTarget {
                    symbol: super::function_symbol(self.hir, callee),
                    signature: signature.clone(),
                    contract: VirContractId::new(call.contract.get()),
                    abi: Some(abi.clone()),
                },
                arguments,
            },
            source_span,
        )?;

        let projected_result = abi
            .borrow_result()
            .is_some_and(|relation| relation.projection != crate::BorrowProjection::Whole);
        let mut escaped_loan = (!projected_result)
            .then(|| {
                abi.borrow_result_parameter()
                    .and_then(|index| {
                        borrowed_arguments
                            .iter()
                            .find(|(parameter, ..)| *parameter == index)
                    })
                    .and_then(|(_, _, _, value)| value.loan)
            })
            .flatten()
            .or_else(|| {
                (!abi.borrow_result_alternatives().is_empty() || projected_result).then(|| {
                    let binding = &abi.results()[0];
                    LoweredLoan::Authority {
                        kind: if binding.interface().transfer
                            == crate::VirInterfaceTransfer::BorrowMutable
                        {
                            VirLoanKind::Mutable
                        } else {
                            VirLoanKind::Shared
                        },
                        reference: binding.value().access().expect("validated borrow result"),
                    }
                })
            });
        let conditional_mutable = !abi.borrow_result_alternatives().is_empty()
            && abi.results()[0].interface().transfer == crate::VirInterfaceTransfer::BorrowMutable;
        let candidate_parameters = abi.borrow_result_parameters();
        let mut deferred = [None; 4];
        let mut deferred_len = 0;
        for (index, slot, local, mut value) in borrowed_arguments {
            if let Some(slot) = slot {
                value.permission =
                    Some(abi_result(&results, slot, VirType::Permission, source_span)?.id);
                if let Some(local) = local {
                    self.environment.reassign(local, value, source_span)?;
                } else if (conditional_mutable || projected_result)
                    && candidate_parameters.contains(&index)
                {
                    let permission = value.permission.ok_or_else(|| invalid_hir(source_span))?;
                    let loan = match value.loan.ok_or_else(|| invalid_hir(source_span))? {
                        LoweredLoan::Static(loan) => DeferredLoanEnd::Static {
                            loan,
                            pointer: value.value,
                            permission,
                        },
                        LoweredLoan::Authority { reference, .. }
                        | LoweredLoan::ConditionalAuthority { reference, .. } => {
                            DeferredLoanEnd::Authority {
                                reference,
                                pointer: value.value,
                                permission,
                            }
                        }
                    };
                    let slot = deferred
                        .get_mut(deferred_len)
                        .ok_or_else(|| invalid_hir(source_span))?;
                    *slot = Some(loan);
                    deferred_len += 1;
                } else {
                    let permission = value.permission.ok_or_else(|| invalid_hir(source_span))?;
                    match value.loan.ok_or_else(|| invalid_hir(source_span))? {
                        LoweredLoan::Static(metadata) => self.cfg.emit_loan_end(
                            loan_effect(metadata, value.value, permission),
                            DraftSourceIdentity::HirNode(expression.id),
                            source_span,
                        )?,
                        LoweredLoan::Authority { reference, .. } => {
                            self.cfg.emit_loan_authority_end(
                                loan_authority_effect(value.value, permission, reference),
                                DraftSourceIdentity::HirNode(expression.id),
                                source_span,
                            )?
                        }
                        LoweredLoan::ConditionalAuthority {
                            reference,
                            deferred,
                            ..
                        } => {
                            self.cfg.emit_loan_authority_end(
                                loan_authority_effect(value.value, permission, reference),
                                DraftSourceIdentity::HirNode(expression.id),
                                source_span,
                            )?;
                            for deferred in deferred.into_iter().flatten() {
                                match deferred {
                                    DeferredLoanEnd::Static {
                                        loan,
                                        pointer,
                                        permission,
                                    } => self.cfg.emit_loan_end(
                                        loan_effect(loan, pointer, permission),
                                        DraftSourceIdentity::HirNode(expression.id),
                                        source_span,
                                    )?,
                                    DeferredLoanEnd::Authority {
                                        reference,
                                        pointer,
                                        permission,
                                    } => self.cfg.emit_loan_authority_end(
                                        loan_authority_effect(pointer, permission, reference),
                                        DraftSourceIdentity::HirNode(expression.id),
                                        source_span,
                                    )?,
                                }
                            }
                        }
                    }
                }
            } else if abi.borrow_result_parameter() == Some(index) {
                if let Some(local) = local {
                    self.environment.forget(&[local], source_span)?;
                }
            } else {
                return Err(invalid_hir(source_span));
            }
        }
        if conditional_mutable || projected_result {
            let binding = &abi.results()[0];
            escaped_loan = Some(LoweredLoan::ConditionalAuthority {
                kind: if binding.interface().transfer == crate::VirInterfaceTransfer::BorrowMutable
                {
                    VirLoanKind::Mutable
                } else {
                    VirLoanKind::Shared
                },
                reference: binding
                    .value()
                    .access()
                    .ok_or_else(|| invalid_hir(source_span))?,
                deferred,
            });
        }

        for (slot, local, storage, transfer) in restored_arguments {
            let permission = abi_result(&results, slot, VirType::Permission, source_span)?;
            let drop_flag = if transfer == crate::VirInterfaceTransfer::Move {
                self.initial_access_drop_flag(storage.access, false, source_span)?
            } else {
                storage.drop_flag
            };
            self.environment.reassign(
                local,
                LoweredValue {
                    value: storage.pointer,
                    ty: VirType::Pointer {
                        access: storage.access,
                    },
                    metadata: None,
                    permission: Some(permission.id),
                    drop_flag,
                    loan: None,
                },
                source_span,
            )?;
        }
        for (slot, local) in restored_slices {
            let permission = abi_result(&results, slot, VirType::Permission, source_span)?;
            let mut value = self.lookup_local(local, source_span)?;
            value.permission = Some(permission.id);
            self.environment.reassign(local, value, source_span)?;
        }

        match result_binding.value() {
            VirAbiValue::Unit { .. } => Ok(None),
            VirAbiValue::Scalar { ty, .. } => {
                let [slot] = result_binding.result_slots() else {
                    return Err(invalid_hir(source_span));
                };
                Ok(Some(runtime_value(abi_result(
                    &results,
                    *slot,
                    *ty,
                    source_span,
                )?)))
            }
            VirAbiValue::Pointer { pointee, .. } => {
                let [pointer_slot, permission_slot] = result_binding.result_slots() else {
                    return Err(invalid_hir(source_span));
                };
                let pointer = abi_result(
                    &results,
                    *pointer_slot,
                    VirType::Pointer { access: *pointee },
                    source_span,
                )?;
                let permission =
                    abi_result(&results, *permission_slot, VirType::Permission, source_span)?;
                let drop_flag = self.initial_drop_flag(expression.ty, true, source_span)?;
                Ok(Some(LoweredValue {
                    value: pointer.id,
                    ty: pointer.ty,
                    metadata: None,
                    permission: Some(permission.id),
                    drop_flag,
                    loan: escaped_loan,
                }))
            }
            VirAbiValue::Slice { element, .. } => {
                let [pointer_slot, length_slot, permission_slot] = result_binding.result_slots()
                else {
                    return Err(invalid_hir(source_span));
                };
                let pointer = abi_result(
                    &results,
                    *pointer_slot,
                    VirType::Pointer { access: *element },
                    source_span,
                )?;
                let length = abi_result(&results, *length_slot, VirType::U64, source_span)?;
                let permission =
                    abi_result(&results, *permission_slot, VirType::Permission, source_span)?;
                Ok(Some(LoweredValue {
                    value: pointer.id,
                    ty: pointer.ty,
                    metadata: Some(length.id),
                    permission: Some(permission.id),
                    drop_flag: None,
                    loan: escaped_loan,
                }))
            }
            VirAbiValue::DirectAggregate { leaves, .. } => {
                let storage = result_storage.ok_or_else(|| invalid_hir(source_span))?;
                let values = result_binding
                    .result_slots()
                    .iter()
                    .zip(leaves)
                    .map(|(slot, leaf)| abi_result(&results, *slot, leaf.ty(), source_span))
                    .collect::<Result<Vec<_>, _>>()?;
                self.initialize_abi_leaves(storage, leaves, &values, source_span)?;
                let storage = self.finish_object_initialization(storage, source_span)?;
                Ok(Some(object_value(storage)))
            }
            VirAbiValue::IndirectAggregate { .. } => {
                let storage = result_storage.ok_or_else(|| invalid_hir(source_span))?;
                let [permission_slot] = result_binding.result_slots() else {
                    return Err(invalid_hir(source_span));
                };
                let permission =
                    abi_result(&results, *permission_slot, VirType::Permission, source_span)?;
                let local = self
                    .abi_call_storage
                    .iter()
                    .find(|candidate| {
                        candidate.owner == expression.id
                            && candidate.role == AbiCallStorageRole::Result
                    })
                    .map(|candidate| candidate.local)
                    .ok_or_else(|| invalid_hir(source_span))?;
                let drop_flag = self.initial_drop_flag(expression.ty, true, source_span)?;
                self.environment.reassign(
                    local,
                    LoweredValue {
                        value: storage.pointer,
                        ty: VirType::Pointer {
                            access: storage.access,
                        },
                        metadata: None,
                        permission: Some(permission.id),
                        drop_flag,
                        loan: None,
                    },
                    source_span,
                )?;
                Ok(Some(object_value(self.storage_object(local, source_span)?)))
            }
            VirAbiValue::Opaque(_) => Err(invalid_hir(source_span)),
        }
    }
}
