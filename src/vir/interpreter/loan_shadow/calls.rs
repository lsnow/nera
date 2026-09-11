//! Frame-local import/export of signature-bound loan authority.

use super::*;

impl RuntimeLoanShadow {
    pub(in crate::vir::interpreter) fn parameter_view(
        &self,
        index: usize,
    ) -> Option<(VirRuntimePointer, VirLoanRange)> {
        let loan = self
            .loans
            .get(&crate::vir::interface_loan_id(index as u32))?;
        Some((
            VirRuntimePointer {
                allocation: loan.allocation,
                offset_bytes: loan.range.start_bytes,
                access: loan.pointee,
                paths: crate::VirPointerPaths::default(),
                view_range: Some(loan.range),
                domain: crate::VirPointerDomain::Restricted(loan.range),
            },
            loan.range,
        ))
    }
    pub(in crate::vir::interpreter) fn import_parameters(
        &mut self,
        frame: &mut BlockFrame,
        function: &crate::VirFunction,
        runtime: crate::RuntimeVirView<'_>,
        limits: RuntimeLoanLimits,
        span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        let abi = &runtime
            .abis
            .function(function.id)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
            .signature;
        let borrows = runtime.borrows;
        let memory = runtime.memory;
        let entry = function
            .blocks
            .iter()
            .find(|block| block.id == function.entry)
            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
        for region in borrows
            .regions()
            .iter()
            .filter(|region| region.owner == function.id)
        {
            let crate::VirBorrowRegionOrigin::Parameter { index } = region.origin else {
                continue;
            };
            if self.active_count() >= limits.active_loans || limits.aliases_per_loan == 0 {
                return Err(error(
                    VirExecutionErrorKind::ActiveLoanLimitExceeded {
                        limit: limits.active_loans,
                    },
                    span,
                ));
            }
            let binding = &abi.parameters()[index as usize];
            let pointer_id = entry.parameters[binding.parameter_slots()[0] as usize].id;
            let permission_id = entry.parameters[*binding
                .parameter_slots()
                .last()
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                as usize]
                .id;
            let mut pointer = pointer_value(frame, pointer_id, span)?;
            let permission = frame.permission(permission_id, span)?;
            let loan_id = crate::vir::interface_loan_id(index);
            let size = memory
                .layout(pointer.access.layout)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                .size_bytes;
            let count = if matches!(binding.value(), crate::VirAbiValue::Slice { .. }) {
                crate::vir::interpreter::word_value(
                    frame,
                    entry.parameters[binding.parameter_slots()[1] as usize].id,
                    span,
                )?
            } else {
                1
            };
            let end_bytes = size
                .checked_mul(count)
                .and_then(|bytes| pointer.offset_bytes.checked_add(bytes))
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
            let range = VirLoanRange {
                start_bytes: pointer.offset_bytes,
                end_bytes,
            };
            if matches!(binding.value(), crate::VirAbiValue::Slice { .. }) {
                pointer.view_range = Some(range);
                frame
                    .values
                    .insert(pointer_id, VirRuntimeValue::Pointer(pointer));
            }
            self.check_source_range(loan_id, pointer, permission, range, span)?;
            let authority = self.fresh_authority(loan_id, span)?;
            self.loans.insert(
                loan_id,
                RuntimeLoan {
                    allocation: pointer.allocation,
                    range,
                    envelope: range,
                    kind: if binding.interface().transfer
                        == crate::VirInterfaceTransfer::BorrowShared
                    {
                        VirLoanKind::Shared
                    } else {
                        VirLoanKind::Mutable
                    },
                    region: region.id,
                    parent: None,
                    pointee: pointer.access,
                    activity: RuntimeLoanActivity::Active,
                    authorities: BTreeSet::from([authority.token]),
                },
            );
            frame.set_loan_authority(permission_id, authority);
            frame.values.insert(
                permission_id,
                VirRuntimeValue::Permission(VirRuntimePermission {
                    start_bytes: range.start_bytes,
                    end_bytes: range.end_bytes,
                    can_free_when_complete: false,
                    ..permission
                }),
            );
        }
        Ok(())
    }

    pub(in crate::vir::interpreter) fn prepare_call(
        &mut self,
        frame: &BlockFrame,
        arguments: &[VirValueId],
        results: &[VirValue],
        abi: Option<&crate::VirAbiSignature>,
        limits: RuntimeLoanLimits,
        span: ByteSpan,
    ) -> Result<Vec<RuntimeBorrowReturn>, VirExecutionError> {
        let mut admitted = BTreeSet::new();
        let mut restored = Vec::new();
        if let Some(abi) = abi {
            for (index, binding) in abi.parameters().iter().enumerate() {
                if !binding.interface().transfer.is_borrow() {
                    continue;
                }
                let permission_id = arguments[*binding
                    .parameter_slots()
                    .last()
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                    as usize];
                let Some(authority) = frame.loan_authority(permission_id) else {
                    continue;
                };
                if (self.loan(authority.loan, span)?.kind == VirLoanKind::Shared)
                    != (binding.interface().transfer == crate::VirInterfaceTransfer::BorrowShared)
                {
                    return Err(error(
                        VirExecutionErrorKind::LoanAccessConflict {
                            loan: authority.loan,
                            permission: permission_id,
                        },
                        span,
                    ));
                }
                let pointer = pointer_value(
                    frame,
                    arguments[binding.parameter_slots()[0] as usize],
                    span,
                )?;
                let permission = frame.permission(permission_id, span)?;
                self.check_access(
                    frame,
                    RuntimeLoanAccessRequest {
                        permission: permission_id,
                        pointer,
                        start_bytes: permission.start_bytes,
                        end_bytes: permission.end_bytes,
                        kind: if binding.interface().transfer
                            == crate::VirInterfaceTransfer::BorrowShared
                        {
                            RuntimeLoanAccess::Read
                        } else {
                            RuntimeLoanAccess::Write
                        },
                    },
                    span,
                )?;
                admitted.insert(permission_id);
                for slot in binding.result_slots() {
                    restored.push(RuntimeBorrowReturn {
                        value: results[*slot as usize].id,
                        authority,
                        permission,
                        callee_loan: None,
                        projected_pointee: None,
                    });
                }
                if abi.borrow_result_parameter() == Some(index) {
                    let result =
                        results[*abi.results()[0].result_slots().last().ok_or_else(|| {
                            error(VirExecutionErrorKind::InvalidRuntimeState, span)
                        })? as usize];
                    let projected = abi.borrow_result().is_some_and(|relation| {
                        relation.parameter as usize == index
                            && relation.projection != crate::BorrowProjection::Whole
                    });
                    let result_authority = if projected {
                        authority
                    } else if binding.interface().transfer
                        == crate::VirInterfaceTransfer::BorrowShared
                    {
                        if self.loan(authority.loan, span)?.authorities.len()
                            >= limits.aliases_per_loan
                        {
                            return Err(error(
                                VirExecutionErrorKind::LoanAliasLimitExceeded {
                                    loan: authority.loan,
                                    limit: limits.aliases_per_loan,
                                },
                                span,
                            ));
                        }
                        let fresh = self.fresh_authority(authority.loan, span)?;
                        self.loans
                            .get_mut(&authority.loan)
                            .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                            .authorities
                            .insert(fresh.token);
                        fresh
                    } else {
                        authority
                    };
                    restored.push(RuntimeBorrowReturn {
                        value: result.id,
                        authority: result_authority,
                        permission,
                        callee_loan: projected
                            .then_some(crate::vir::interface_loan_id(index as u32)),
                        projected_pointee: projected.then(|| match abi.results()[0].value() {
                            crate::VirAbiValue::Pointer { pointee, .. } => *pointee,
                            crate::VirAbiValue::Slice { element, .. } => *element,
                            _ => unreachable!("validated projected borrow result"),
                        }),
                    });
                }
                if abi.borrow_result_parameters().contains(&index)
                    && abi.borrow_result_parameter().is_none()
                {
                    let result =
                        results[*abi.results()[0].result_slots().last().ok_or_else(|| {
                            error(VirExecutionErrorKind::InvalidRuntimeState, span)
                        })? as usize];
                    restored.push(RuntimeBorrowReturn {
                        value: result.id,
                        authority,
                        permission,
                        callee_loan: Some(crate::vir::interface_loan_id(index as u32)),
                        projected_pointee: None,
                    });
                }
            }
        }
        if let Some(permission) = arguments
            .iter()
            .copied()
            .find(|id| frame.loan_authority(*id).is_some() && !admitted.contains(id))
        {
            return Err(error(
                VirExecutionErrorKind::LoanAuthorityAcrossCall { permission },
                span,
            ));
        }
        Ok(restored)
    }

    pub(in crate::vir::interpreter) fn activate_conditional_return(
        &mut self,
        authority: RuntimeLoanAuthority,
        projected_pointee: Option<crate::VirMemoryAccess>,
        returned_permission: VirRuntimePermission,
        limits: RuntimeLoanLimits,
        span: ByteSpan,
    ) -> Result<RuntimeLoanAuthority, VirExecutionError> {
        let parent = self.loan(authority.loan, span)?.clone();
        if parent.kind == VirLoanKind::Shared && projected_pointee.is_none() {
            if parent.authorities.len() >= limits.aliases_per_loan {
                return Err(error(
                    VirExecutionErrorKind::LoanAliasLimitExceeded {
                        loan: authority.loan,
                        limit: limits.aliases_per_loan,
                    },
                    span,
                ));
            }
            let fresh = self.fresh_authority(authority.loan, span)?;
            self.loans
                .get_mut(&authority.loan)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                .authorities
                .insert(fresh.token);
            return Ok(fresh);
        }
        if self.active_count() >= limits.active_loans {
            return Err(error(
                VirExecutionErrorKind::ActiveLoanLimitExceeded {
                    limit: limits.active_loans,
                },
                span,
            ));
        }
        let mut id = VirLoanId::new(self.next_dynamic_loan);
        while self.loans.contains_key(&id) {
            self.next_dynamic_loan = self.next_dynamic_loan.checked_add(1).ok_or_else(|| {
                error(
                    VirExecutionErrorKind::ActiveLoanLimitExceeded {
                        limit: limits.active_loans,
                    },
                    span,
                )
            })?;
            id = VirLoanId::new(self.next_dynamic_loan);
        }
        self.next_dynamic_loan = self.next_dynamic_loan.checked_add(1).ok_or_else(|| {
            error(
                VirExecutionErrorKind::ActiveLoanLimitExceeded {
                    limit: limits.active_loans,
                },
                span,
            )
        })?;
        let fresh = self.fresh_authority(id, span)?;
        if parent.kind == VirLoanKind::Mutable {
            self.loans
                .get_mut(&authority.loan)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                .activity = RuntimeLoanActivity::Suspended;
        }
        let range = projected_pointee.map_or(parent.range, |_| VirLoanRange {
            start_bytes: returned_permission.start_bytes,
            end_bytes: returned_permission.end_bytes,
        });
        self.loans.insert(
            id,
            RuntimeLoan {
                allocation: parent.allocation,
                range,
                envelope: range,
                kind: parent.kind,
                region: parent.region,
                parent: Some(authority.loan),
                pointee: projected_pointee.unwrap_or(parent.pointee),
                activity: RuntimeLoanActivity::Active,
                authorities: BTreeSet::from([fresh.token]),
            },
        );
        Ok(fresh)
    }

    pub(in crate::vir::interpreter) fn export_parameters(
        &mut self,
        frame: &BlockFrame,
        values: &[VirValueId],
        abi: &crate::VirAbiSignature,
        span: ByteSpan,
    ) -> Result<(), VirExecutionError> {
        for (index, binding) in abi.parameters().iter().enumerate() {
            let id = crate::vir::interface_loan_id(index as u32);
            let Some(loan) = self.loans.get(&id) else {
                continue;
            };
            let mut exported = BTreeSet::new();
            for slot in binding.result_slots().iter().copied() {
                let permission = *values
                    .get(slot as usize)
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                let returned = frame.permission(permission, span)?;
                if returned.allocation != loan.allocation
                    || returned.start_bytes > loan.range.start_bytes
                    || returned.end_bytes < loan.range.end_bytes
                    || returned.can_free_when_complete
                {
                    return Err(error(
                        VirExecutionErrorKind::LoanAccessConflict {
                            loan: id,
                            permission,
                        },
                        span,
                    ));
                }
                let authority = self.require_authority(frame, id, permission, span)?;
                exported.insert(authority.token);
            }
            if abi.borrow_result_parameters().contains(&index) {
                let slot = *abi.results()[0]
                    .result_slots()
                    .last()
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                let permission = *values
                    .get(slot as usize)
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                if let Some(authority) = frame.loan_authority(permission)
                    && authority.loan == id
                {
                    exported.insert(authority.token);
                }
            }
            let selected_child = if abi.borrow_result_parameters().contains(&index) {
                let slot = *abi.results()[0]
                    .result_slots()
                    .last()
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                let permission = *values
                    .get(slot as usize)
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?;
                frame.loan_authority(permission).and_then(|authority| {
                    self.loans
                        .get(&authority.loan)
                        .filter(|child| {
                            child.parent == Some(id)
                                && child.activity == RuntimeLoanActivity::Active
                                && child.authorities == BTreeSet::from([authority.token])
                        })
                        .map(|_| authority.loan)
                })
            } else {
                None
            };
            if !matches!(
                loan.activity,
                RuntimeLoanActivity::Active | RuntimeLoanActivity::Suspended
            ) || (loan.activity == RuntimeLoanActivity::Suspended && selected_child.is_none())
                || (abi.borrow_result().is_some_and(|relation| {
                    relation.parameter as usize == index
                        && relation.projection != crate::BorrowProjection::Whole
                }) && selected_child.is_none())
                || exported.is_empty()
                || exported != loan.authorities
            {
                return Err(error(
                    VirExecutionErrorKind::LoanNotEnded { loan: id },
                    span,
                ));
            }
            self.loans
                .get_mut(&id)
                .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                .activity = RuntimeLoanActivity::Ended;
            if let Some(child) = selected_child {
                self.loans
                    .get_mut(&child)
                    .ok_or_else(|| error(VirExecutionErrorKind::InvalidRuntimeState, span))?
                    .activity = RuntimeLoanActivity::Ended;
            }
        }
        Ok(())
    }
}
