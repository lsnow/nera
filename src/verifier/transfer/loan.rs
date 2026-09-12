use super::*;

impl<'environment> TransferBuilder<'environment> {
    pub(super) fn loan_begin(
        &mut self,
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let context = self
            .loan_context
            .ok_or(TransferError::MissingLoanTransferContext)?;
        let range = loan_range(effect)?;
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        let source_status = combine_statuses([
            self.require_loan_source(effect, pointer, permission, range),
            self.require_loan_value(effect, pointer, range)?,
        ]);
        let instance_status = self.require_previous_loan_instance_ended(effect.loan);
        let authority_status = owner_authority_status(permission.authority());
        let conflict_status = loan_creation_compatibility(
            &self.state,
            effect,
            None,
            self.borrow_footprint(effect, pointer, range),
            self.relation_limits,
            &self.relations,
        );
        let compatibility = combine_statuses([authority_status, conflict_status]);
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: Some(effect.loan),
                permission: effect.source_permission,
                access: Some(range),
                required: loan_access(effect.kind),
            },
            compatibility,
        );

        let budget_status = self.require_active_loan_budget(effect.loan, context.limits);
        let exact = [source_status, instance_status, compatibility, budget_status]
            .into_iter()
            .all(ObligationStatus::is_proven);
        let activity = if exact {
            LoanActivity::Active
        } else {
            LoanActivity::MaybeActive
        };
        let tracked = budget_status.is_proven() && instance_status.is_proven();
        if tracked {
            let loan = AbstractLoan::new(
                pointer.provenance(),
                range,
                effect.kind,
                effect.region,
                effect.parent,
                activity,
            )
            .with_footprint(self.borrow_footprint(effect, pointer, range));
            self.state.define_next_loan_instance(
                effect.loan,
                if exact {
                    loan.with_authority(permission_result.id)
                } else {
                    loan
                },
            )?;
        }
        self.define_loan_results(effect, pointer, reference_result, permission_result, exact)
    }

    pub(super) fn loan_alias_shared(
        &mut self,
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let context = self
            .loan_context
            .ok_or(TransferError::MissingLoanTransferContext)?;
        let range = loan_range(effect)?;
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        let source_status = combine_statuses([
            self.require_loan_source(effect, pointer, permission, range),
            self.require_loan_value(effect, pointer, range)?,
        ]);
        let compatibility =
            self.state
                .loan(effect.loan)
                .map_or(ObligationStatus::Unknown, |loan| {
                    combine_statuses([
                        tracked_loan_authority_status(
                            loan,
                            effect.source_permission,
                            permission.authority(),
                            effect.loan,
                        ),
                        loan_activity_access_status(loan.activity()),
                        if loan.kind() == VirLoanKind::Shared {
                            ObligationStatus::Proven
                        } else {
                            ObligationStatus::Refuted
                        },
                        loan_metadata_status(loan, effect, pointer.provenance(), range),
                    ])
                });
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: Some(effect.loan),
                permission: effect.source_permission,
                access: Some(range),
                required: AccessPermission::Read,
            },
            compatibility,
        );
        let alias_status = self.require_alias_budget(effect.loan, context.limits);
        let tracked = [source_status, compatibility, alias_status]
            .into_iter()
            .all(ObligationStatus::is_proven);
        if !tracked && let Some(loan) = self.state.loan_mut(effect.loan) {
            loan.set_activity(LoanActivity::MaybeActive);
        }
        if tracked && let Some(loan) = self.state.loan_mut(effect.loan) {
            loan.add_authority(permission_result.id);
        }
        self.define_loan_results(
            effect,
            pointer,
            reference_result,
            permission_result,
            tracked,
        )
    }

    pub(super) fn loan_alias_authority(
        &mut self,
        effect: VirLoanAuthorityEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        if let Some(effect) = self.resolve_authority_effect(effect, permission) {
            return self.loan_alias_shared(effect, reference_result, permission_result);
        }
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: None,
                permission: effect.source_permission,
                access: None,
                required: AccessPermission::Read,
            },
            ObligationStatus::Unknown,
        );
        let pointee = reference_pointee(self.memory, effect.reference)?;
        self.define(
            reference_result,
            AbstractValue::Pointer(pointer.with_memory_access(Some(pointee))),
        )?;
        self.define(
            permission_result,
            AbstractValue::Permission(
                permission
                    .with_availability(PermissionAvailability::Available)
                    .with_authority(PermissionAuthority::Unknown),
            ),
        )
    }

    pub(super) fn loan_reborrow_authority(
        &mut self,
        loan: VirLoanId,
        region: crate::VirBorrowRegionId,
        effect: VirLoanAuthorityEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        let kind = match self.memory.kind(effect.reference.ty) {
            Some(VirMemoryTypeKind::Slice {
                mutability: VirMutability::Mutable,
                ..
            })
            | Some(VirMemoryTypeKind::Pointer {
                mutability: VirMutability::Mutable,
                ..
            }) => VirLoanKind::Mutable,
            _ => VirLoanKind::Shared,
        };
        if let Some(parent) = self.resolve_authority_effect(effect, permission) {
            let access = reference_pointee(self.memory, effect.reference)?;
            let width = self
                .memory
                .object_shape(access)
                .map_err(|_| TransferError::InvalidDerivedRange)?
                .size_bytes();
            let slice = matches!(
                self.memory.kind(effect.reference.ty),
                Some(VirMemoryTypeKind::Slice { .. })
            );
            let range = if slice {
                pointer.slice_footprint().map(|f| f.envelope)
            } else {
                access_envelope(pointer.offset_bytes(), width)
            };
            if let Some(range) = range {
                return self.loan_reborrow(
                    VirLoanEffect {
                        loan,
                        kind,
                        region,
                        parent: Some(parent.loan),
                        source_pointer: effect.source_pointer,
                        source_permission: effect.source_permission,
                        reference: effect.reference,
                        range: crate::VirLoanRange {
                            start_bytes: range.start(),
                            end_bytes: range.end(),
                        },
                        origin: effect.origin,
                    },
                    reference_result,
                    permission_result,
                );
            }
        }
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: Some(loan),
                permission: effect.source_permission,
                access: None,
                required: loan_access(kind),
            },
            ObligationStatus::Unknown,
        );
        self.define(reference_result, AbstractValue::Pointer(pointer))?;
        self.define(
            permission_result,
            AbstractValue::Permission(fresh_unknown_permission()),
        )
    }

    pub(super) fn loan_reborrow(
        &mut self,
        effect: VirLoanEffect,
        reference_result: VirValue,
        permission_result: VirValue,
    ) -> Result<(), TransferError> {
        let context = self
            .loan_context
            .ok_or(TransferError::MissingLoanTransferContext)?;
        let range = loan_range(effect)?;
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        let source_status = combine_statuses([
            self.require_loan_source(effect, pointer, permission, range),
            self.require_loan_value(effect, pointer, range)?,
        ]);
        let instance_status = self.require_previous_loan_instance_ended(effect.loan);
        let parent_id = effect
            .parent
            .ok_or(TransferError::InvalidValidatedLoan(effect.loan))?;
        let parent = self.state.loan(parent_id);
        let parent_region = parent.map(AbstractLoan::region);
        let shared_child = parent.is_some_and(|parent| {
            parent.kind() == VirLoanKind::Shared && effect.kind == VirLoanKind::Shared
        });
        let parent_status = parent.map_or(ObligationStatus::Unknown, |parent| {
            let authority = tracked_loan_authority_status(
                parent,
                effect.source_permission,
                permission.authority(),
                parent_id,
            );
            let activity = match parent.activity() {
                LoanActivity::Active | LoanActivity::Suspended => ObligationStatus::Proven,
                LoanActivity::MaybeActive => ObligationStatus::Unknown,
                LoanActivity::Ended => ObligationStatus::Refuted,
            };
            let containment = combine_statuses([
                parent_contains_child_status(parent, effect, pointer.provenance(), range),
                self.borrow_footprint(effect, pointer, range)
                    .map_or(ObligationStatus::Unknown, |f| {
                        self.range_contains(parent.actual_range(), f.range)
                    }),
            ]);
            combine_statuses([authority, activity, containment])
        });
        self.require(
            ResourceObligationKind::LoanParentActive {
                loan: effect.loan,
                parent: parent_id,
            },
            parent_status,
        );

        let region_status = if context
            .borrows
            .constraints()
            .iter()
            .filter(|constraint| constraint.owner == context.function)
            .count()
            > context.limits.max_region_constraints
        {
            self.state
                .mark_loan_precision_loss(LoanPrecisionLoss::RegionConstraintBudget);
            ObligationStatus::Unknown
        } else {
            match parent_region.and_then(|parent_region| {
                context.borrows.includes(
                    effect.region,
                    parent_region,
                    context.limits.max_region_constraints,
                )
            }) {
                Some(true) => ObligationStatus::Proven,
                Some(false) => ObligationStatus::Refuted,
                None => {
                    if parent_region.is_some() {
                        self.state
                            .mark_loan_precision_loss(LoanPrecisionLoss::RegionConstraintBudget);
                    }
                    ObligationStatus::Unknown
                }
            }
        };
        self.require(
            ResourceObligationKind::LoanRegionIncluded {
                loan: effect.loan,
                parent: parent_id,
            },
            region_status,
        );
        let depth_status = self.require_reborrow_depth(effect.loan, parent_id, context.limits);
        let conflict_status = loan_creation_compatibility(
            &self.state,
            effect,
            Some(parent_id),
            self.borrow_footprint(effect, pointer, range),
            self.relation_limits,
            &self.relations,
        );
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: Some(effect.loan),
                permission: effect.source_permission,
                access: Some(range),
                required: loan_access(effect.kind),
            },
            conflict_status,
        );
        let budget_status = self.require_active_loan_budget(effect.loan, context.limits);
        let exact = [
            source_status,
            instance_status,
            parent_status,
            region_status,
            depth_status,
            conflict_status,
            budget_status,
        ]
        .into_iter()
        .all(ObligationStatus::is_proven);
        if let Some(parent) = self.state.loan_mut(parent_id) {
            parent.set_activity(if exact && shared_child {
                LoanActivity::Active
            } else if exact {
                LoanActivity::Suspended
            } else {
                LoanActivity::MaybeActive
            });
        }
        let tracked = budget_status.is_proven() && instance_status.is_proven();
        if tracked {
            let loan = AbstractLoan::new(
                pointer.provenance(),
                range,
                effect.kind,
                effect.region,
                effect.parent,
                if exact {
                    LoanActivity::Active
                } else {
                    LoanActivity::MaybeActive
                },
            )
            .with_footprint(self.borrow_footprint(effect, pointer, range));
            self.state.define_next_loan_instance(
                effect.loan,
                if exact {
                    loan.with_authority(permission_result.id)
                } else {
                    loan
                },
            )?;
        }
        self.define_loan_results(effect, pointer, reference_result, permission_result, exact)
    }

    pub(super) fn loan_end(&mut self, effect: VirLoanEffect) -> Result<(), TransferError> {
        let _context = self
            .loan_context
            .ok_or(TransferError::MissingLoanTransferContext)?;
        let range = loan_range(effect)?;
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        // Ending an authority is not a memory access and does not reevaluate
        // its selection. Lost SSA bounds must not keep a valid loan alive.
        let source_status = permission_availability_status(permission.availability());
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: effect.source_permission,
            },
            source_status,
        );
        let end_status = self
            .state
            .loan(effect.loan)
            .map_or(ObligationStatus::Unknown, |loan| {
                combine_statuses([
                    tracked_loan_authority_status(
                        loan,
                        effect.source_permission,
                        permission.authority(),
                        effect.loan,
                    ),
                    loan_activity_access_status(loan.activity()),
                    loan_metadata_status(loan, effect, pointer.provenance(), range),
                    no_active_child_status(&self.state, effect.loan),
                ])
            });
        let exact = source_status.is_proven() && end_status.is_proven();
        self.require(
            ResourceObligationKind::LoanEndedExactlyOnce { loan: effect.loan },
            end_status,
        );
        mark_permission_consumed(&mut self.state, effect.source_permission)?;
        let remaining =
            self.state
                .loan_mut(effect.loan)
                .map_or(ObligationStatus::Unknown, |loan| {
                    let removed = loan.remove_authority(effect.source_permission);
                    match (removed, loan.authorities().is_empty()) {
                        (true, true) => ObligationStatus::Proven,
                        (true, false) => ObligationStatus::Refuted,
                        (false, _) => ObligationStatus::Unknown,
                    }
                });
        let parent_id = self.state.loan(effect.loan).and_then(|loan| loan.parent());
        if let Some(loan) = self.state.loan_mut(effect.loan) {
            loan.set_activity(if exact {
                match remaining {
                    ObligationStatus::Proven => LoanActivity::Ended,
                    ObligationStatus::Refuted => LoanActivity::Active,
                    ObligationStatus::Unknown => LoanActivity::MaybeActive,
                }
            } else {
                LoanActivity::MaybeActive
            });
        }
        if exact && remaining.is_proven() {
            self.restore_parent_after_child(effect.loan, parent_id);
        }
        Ok(())
    }

    pub(super) fn loan_end_authority(
        &mut self,
        effect: VirLoanAuthorityEffect,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, effect.source_pointer)?;
        let permission = permission_fact(&self.state, effect.source_permission)?;
        if let Some(resolved) = self.resolve_authority_effect(effect, permission) {
            let range = loan_range(resolved)?;
            let availability = permission_availability_status(permission.availability());
            self.require(
                ResourceObligationKind::PermissionAvailable {
                    permission: effect.source_permission,
                },
                availability,
            );
            let no_active_child = no_active_child_status(&self.state, resolved.loan);
            let authority =
                self.state
                    .loan(resolved.loan)
                    .map_or(ObligationStatus::Unknown, |loan| {
                        combine_statuses([
                            tracked_loan_authority_status(
                                loan,
                                effect.source_permission,
                                permission.authority(),
                                resolved.loan,
                            ),
                            loan_activity_access_status(loan.activity()),
                            loan_metadata_status(loan, resolved, pointer.provenance(), range),
                            if loan.authorities().len() > 1 {
                                ObligationStatus::Proven
                            } else {
                                no_active_child
                            },
                        ])
                    });
            self.require(
                ResourceObligationKind::LoanCompatible {
                    loan: Some(resolved.loan),
                    permission: effect.source_permission,
                    access: Some(range),
                    required: AccessPermission::Read,
                },
                authority,
            );
            mark_permission_consumed(&mut self.state, effect.source_permission)?;
            let parent = self
                .state
                .loan(resolved.loan)
                .and_then(AbstractLoan::parent);
            let ended = self.state.loan_mut(resolved.loan).is_some_and(|loan| {
                let removed = loan.remove_authority(effect.source_permission);
                if !removed {
                    loan.set_activity(LoanActivity::MaybeActive);
                    return false;
                }
                if loan.authorities().is_empty() {
                    loan.set_activity(LoanActivity::Ended);
                    true
                } else {
                    false
                }
            });
            if ended {
                self.restore_parent_after_child(resolved.loan, parent);
            }
            return Ok(());
        }
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan: None,
                permission: effect.source_permission,
                access: None,
                required: AccessPermission::Read,
            },
            ObligationStatus::Unknown,
        );
        mark_permission_consumed(&mut self.state, effect.source_permission)
    }

    pub(super) fn end_stored_loan_authority(
        &mut self,
        loan_id: VirLoanId,
        allocation: AbstractAllocationId,
        payload: ResourcePayloadKey,
    ) {
        let parent_id = self.state.loan(loan_id).and_then(AbstractLoan::parent);
        let ended = self.state.loan_mut(loan_id).is_some_and(|loan| {
            loan.remove_stored_authority(allocation, payload) && loan.authorities().is_empty()
        });
        if let Some(loan) = self.state.loan_mut(loan_id) {
            loan.set_activity(if ended {
                LoanActivity::Ended
            } else {
                LoanActivity::Active
            });
        }
        if ended {
            self.restore_parent_after_child(loan_id, parent_id);
        }
    }

    pub(super) fn resolve_authority_effect(
        &self,
        effect: VirLoanAuthorityEffect,
        permission: AbstractPermission,
    ) -> Option<VirLoanEffect> {
        let PermissionAuthority::Loan(loan_id) = permission.authority() else {
            return None;
        };
        let loan = self.state.loan(loan_id)?;
        Some(VirLoanEffect {
            loan: loan_id,
            kind: loan.kind(),
            region: loan.region(),
            parent: loan.parent(),
            source_pointer: effect.source_pointer,
            source_permission: effect.source_permission,
            reference: effect.reference,
            range: crate::VirLoanRange {
                start_bytes: loan.range().start(),
                end_bytes: loan.range().end(),
            },
            origin: effect.origin,
        })
    }

    pub(super) fn require_previous_loan_instance_ended(
        &mut self,
        loan: VirLoanId,
    ) -> ObligationStatus {
        let status = self
            .state
            .loan(loan)
            .map_or(ObligationStatus::Proven, |previous| {
                match previous.activity() {
                    LoanActivity::Ended => ObligationStatus::Proven,
                    LoanActivity::Active | LoanActivity::Suspended => ObligationStatus::Refuted,
                    LoanActivity::MaybeActive => ObligationStatus::Unknown,
                }
            });
        self.require(
            ResourceObligationKind::LoanEndedExactlyOnce { loan },
            status,
        );
        status
    }

    pub(super) fn move_loan_authority(
        &mut self,
        authority: PermissionAuthority,
        source: VirValueId,
        result: VirValueId,
    ) {
        let PermissionAuthority::Loan(loan_id) = authority else {
            return;
        };
        let Some(loan) = self.state.loan_mut(loan_id) else {
            return;
        };
        if !loan.move_authority(source, result) {
            loan.set_activity(LoanActivity::MaybeActive);
        }
    }

    pub(super) fn define_loan_results(
        &mut self,
        effect: VirLoanEffect,
        pointer: AbstractPointer,
        reference_result: VirValue,
        permission_result: VirValue,
        tracked: bool,
    ) -> Result<(), TransferError> {
        let access = match reference_result.ty {
            VirType::Pointer { access } => access,
            _ => return Err(TransferError::InvalidValidatedLoan(effect.loan)),
        };
        self.define(
            reference_result,
            AbstractValue::Pointer(pointer.with_memory_access(Some(access))),
        )?;
        let range = self
            .state
            .loan(effect.loan)
            .map_or(AbstractByteRange::Unknown, AbstractLoan::actual_range);
        let permission = AbstractPermission::new(
            pointer.provenance(),
            range,
            loan_access(effect.kind),
            FreeCapability::No,
        )
        .with_authority(if tracked {
            PermissionAuthority::Loan(effect.loan)
        } else {
            PermissionAuthority::Unknown
        });
        self.define(permission_result, AbstractValue::Permission(permission))
    }

    /// Formation checks value state independently of loan authority. Ending a
    /// loan deliberately does not use this check: ending cannot manufacture T.
    pub(super) fn require_loan_value(
        &mut self,
        effect: VirLoanEffect,
        pointer: AbstractPointer,
        range: ByteRange,
    ) -> Result<ObligationStatus, TransferError> {
        let start = self.obligations.len();
        let footprint = self.borrow_footprint(effect, pointer, range);
        let range = footprint.map_or(range, |f| f.envelope);
        let access = reference_pointee(self.memory, effect.reference)?;
        let slice = matches!(
            self.memory.kind(effect.reference.ty),
            Some(VirMemoryTypeKind::Slice { .. })
        );
        let shape = self
            .memory
            .object_shape(access)
            .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
        let stride = shape.size_bytes();
        let domain_status = self.require_domain_range(
            effect.source_pointer,
            pointer,
            if slice {
                footprint.map_or(AbstractByteRange::Exact(range), |f| f.range)
            } else {
                pointer_range(pointer, stride)
            },
        );
        let allocation_id = match pointer.provenance() {
            AbstractProvenance::Known(id) => Some(id),
            AbstractProvenance::Unknown => None,
        };
        let allocation = allocation_id.and_then(|id| self.state.allocation(id));
        let bounds = allocation.map_or(ObligationStatus::Unknown, |allocation| {
            if range.end() <= allocation.size_bytes() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Refuted
            }
        });
        let alignment = allocation.map_or(ObligationStatus::Unknown, |allocation| {
            object_alignment_status(pointer, allocation, shape.alignment())
        });
        let live = allocation.map_or(ObligationStatus::Unknown, |allocation| {
            liveness_status(allocation.liveness())
        });
        let prefix_complete = allocation_id.is_some_and(|id| {
            self.state.initialized_prefix_covers(
                id,
                access,
                footprint.map_or(AbstractByteRange::Unknown, |f| f.range),
                self.relation_limits,
                &self.relations.queries,
            )
        });
        let complete_trivial = slice
            && shape.resource_leaves().is_empty()
            && shape.variants().is_empty()
            && allocation.is_some_and(|allocation| {
                allocation.initialization().classify(range) == InitializationClass::Initialized
                    && allocation.valid_value_bytes().contains(range)
            });
        self.require(
            ResourceObligationKind::ObjectAllocationLive {
                pointer: effect.source_pointer,
                allocation: allocation_id,
            },
            live,
        );
        self.require(
            ResourceObligationKind::ObjectWithinBounds {
                pointer: effect.source_pointer,
                allocation: allocation_id,
                access: Some(range),
                size_bytes: range.length(),
            },
            bounds,
        );
        self.require(
            ResourceObligationKind::ObjectAligned {
                pointer: effect.source_pointer,
                required_alignment: shape.alignment(),
            },
            alignment,
        );
        // A complete trivial byte envelope proves all its possible elements
        // without enumerating a signature-owned, unknown-length slice.
        if complete_trivial || prefix_complete {
            self.require(
                ResourceObligationKind::MemoryInitialized {
                    allocation: allocation_id.expect("complete allocation"),
                    access: Some(range),
                },
                ObligationStatus::Proven,
            );
            self.require(
                ResourceObligationKind::ObjectRepresentationValid {
                    allocation: allocation_id,
                    access: Some(range),
                    object: access,
                },
                ObligationStatus::Proven,
            );
            return Ok(combine_statuses([bounds, alignment, live, domain_status]));
        }
        // Slice effects describe a conservative envelope. Check every element
        // in that envelope, excluding each element's padding, not raw bytes.
        let count = if slice && stride != 0 {
            range.length() / stride
        } else {
            1
        };
        if (slice && (stride == 0 || !range.length().is_multiple_of(stride)))
            || count > crate::vir::VIR_OBJECT_SHAPE_MAX_NODES as u64
        {
            self.require(
                ResourceObligationKind::ObjectRepresentationValid {
                    allocation: allocation_id,
                    access: Some(range),
                    object: access,
                },
                ObligationStatus::Unknown,
            );
        } else {
            let offsets = if slice {
                Some(
                    (0..count)
                        .map(|index| range.start() + index * stride)
                        .collect::<Vec<_>>(),
                )
            } else {
                pointer.object_offsets().candidates()
            };
            let candidates = offsets.map_or_else(
                || vec![pointer],
                |offsets| {
                    offsets
                        .into_iter()
                        .map(|offset| {
                            AbstractPointer::new(
                                pointer.provenance(),
                                U64Interval::exact(offset),
                                pointer.alignment(),
                            )
                            .with_memory_access(pointer.memory_access())
                        })
                        .collect()
                },
            );
            for selected in candidates {
                // Value validity is checked conservatively for every possible
                // selected object. Permission for the ACTUAL symbolic range
                // is checked separately by require_loan_source, not widened
                // to cover every candidate in this envelope.
                let object = ObjectAccessFacts {
                    pointer: selected,
                    allocation_id,
                    allocation: allocation_id.and_then(|id| self.state.allocation(id).cloned()),
                    envelope: access_envelope(selected.offset_bytes(), stride),
                    shape: shape.clone(),
                };
                if let Some(allocation) = &object.allocation {
                    self.active_variant_access_obligations(
                        effect.source_pointer,
                        selected,
                        allocation,
                        access,
                        stride,
                    )?;
                }
                let mask = active_object_mask(&object);
                self.require_active_variants(&object, &mask);
                self.require_object_initialization(
                    &object,
                    &mask.possible_value_bytes,
                    InitializationRequirement::Initialized,
                );
                self.require_object_validity(&object, &mask.possible_value_bytes);
                self.require_object_resource_payloads(&object, &mask);
            }
        }
        Ok(self.obligations[start..]
            .iter()
            .fold(ObligationStatus::Proven, |status, obligation| {
                combine_statuses([status, obligation.status])
            }))
    }

    pub(super) fn require_loan_source(
        &mut self,
        effect: VirLoanEffect,
        pointer: AbstractPointer,
        permission: AbstractPermission,
        range: ByteRange,
    ) -> ObligationStatus {
        let slice_reference = matches!(
            self.memory.kind(effect.reference.ty),
            Some(VirMemoryTypeKind::Slice { .. })
        );
        let expected_access = match self.memory.kind(effect.reference.ty) {
            Some(VirMemoryTypeKind::Pointer {
                pointee,
                kind: VirPointerKind::Reference,
                ..
            }) => self.memory.access(*pointee),
            Some(VirMemoryTypeKind::Slice { element, .. }) => self.memory.access(*element),
            _ => None,
        };
        let memory_access = expected_access.map_or(ObligationStatus::Refuted, |expected| {
            let status = memory_access_status(pointer.memory_access(), expected);
            self.require(
                ResourceObligationKind::PointerMemoryAccessMatches {
                    pointer: effect.source_pointer,
                    expected,
                    found: pointer.memory_access(),
                },
                status,
            );
            status
        });
        self.require(
            ResourceObligationKind::PointerProvenanceKnown {
                pointer: effect.source_pointer,
            },
            known_provenance_status(pointer.provenance()),
        );
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: effect.source_permission,
            },
            permission_availability_status(permission.availability()),
        );
        let provenance = match pointer.provenance() {
            AbstractProvenance::Known(allocation) => {
                self.require(
                    ResourceObligationKind::PermissionMatchesAllocation {
                        permission: effect.source_permission,
                        allocation,
                    },
                    provenance_match_status(permission.provenance(), allocation),
                );
                self.require(
                    ResourceObligationKind::AllocationTracked { allocation },
                    if self.state.allocation(allocation).is_some() {
                        ObligationStatus::Proven
                    } else {
                        ObligationStatus::Unknown
                    },
                );
                self.require(
                    ResourceObligationKind::AllocationLive { allocation },
                    self.state
                        .allocation(allocation)
                        .map_or(ObligationStatus::Unknown, |allocation| {
                            liveness_status(allocation.liveness())
                        }),
                );
                provenance_match_status(permission.provenance(), allocation)
            }
            AbstractProvenance::Unknown => ObligationStatus::Unknown,
        };
        let footprint = self.borrow_footprint(effect, pointer, range);
        let range_status = combine_statuses([
            if slice_reference {
                pointer_within_slice_range_status(pointer, range)
            } else {
                pointer_within_range_status(pointer, range)
            },
            footprint.map_or(ObligationStatus::Unknown, |f| {
                combine_statuses([
                    if range.contains(f.envelope) {
                        ObligationStatus::Proven
                    } else {
                        ObligationStatus::Refuted
                    },
                    self.range_contains(permission.range(), f.range),
                ])
            }),
            provenance,
        ]);
        self.require(
            ResourceObligationKind::LoanRangeContained {
                loan: effect.loan,
                permission: effect.source_permission,
                range,
            },
            range_status,
        );
        if effect.kind == VirLoanKind::Mutable {
            self.require(
                ResourceObligationKind::PermissionWritable {
                    permission: effect.source_permission,
                },
                permission_writable_status(permission.access()),
            );
        }
        combine_statuses([
            memory_access,
            known_provenance_status(pointer.provenance()),
            permission_availability_status(permission.availability()),
            range_status,
            if effect.kind == VirLoanKind::Mutable {
                permission_writable_status(permission.access())
            } else {
                ObligationStatus::Proven
            },
        ])
    }

    pub(super) fn require_active_loan_budget(
        &mut self,
        loan: VirLoanId,
        limits: LoanTransferLimits,
    ) -> ObligationStatus {
        let active = self
            .state
            .loans()
            .values()
            .filter(|loan| !matches!(loan.activity(), LoanActivity::Ended))
            .count();
        let status = if active < limits.max_active_loans {
            ObligationStatus::Proven
        } else {
            self.state
                .mark_loan_precision_loss(LoanPrecisionLoss::ActiveLoanBudget);
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::LoanWithinBudget {
                loan,
                limit: limits.max_active_loans,
            },
            status,
        );
        status
    }

    pub(super) fn require_alias_budget(
        &mut self,
        loan: VirLoanId,
        limits: LoanTransferLimits,
    ) -> ObligationStatus {
        let aliases = available_loan_authorities(&self.state, loan);
        let status = if aliases < limits.max_aliases_per_loan {
            ObligationStatus::Proven
        } else {
            self.state
                .mark_loan_precision_loss(LoanPrecisionLoss::LoanAliasBudget);
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::LoanAliasWithinBudget {
                loan,
                limit: limits.max_aliases_per_loan,
            },
            status,
        );
        status
    }

    pub(super) fn require_reborrow_depth(
        &mut self,
        loan: VirLoanId,
        parent: VirLoanId,
        limits: LoanTransferLimits,
    ) -> ObligationStatus {
        let mut depth = 1_usize;
        let mut current = Some(parent);
        let mut seen = BTreeSet::new();
        while let Some(id) = current {
            if !seen.insert(id) {
                depth = usize::MAX;
                break;
            }
            current = self.state.loan(id).and_then(|loan| loan.parent());
            if current.is_some() {
                depth = depth.saturating_add(1);
            }
        }
        let status = if depth <= limits.max_reborrow_depth {
            ObligationStatus::Proven
        } else {
            self.state
                .mark_loan_precision_loss(LoanPrecisionLoss::ReborrowDepthBudget);
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::LoanReborrowDepthWithinBudget {
                loan,
                limit: limits.max_reborrow_depth,
            },
            status,
        );
        status
    }

    pub(super) fn restore_parent_after_child(
        &mut self,
        child: VirLoanId,
        parent: Option<VirLoanId>,
    ) {
        let Some(parent_id) = parent else { return };
        let child_status = no_active_child_status(&self.state, parent_id);
        if let Some(parent) = self.state.loan_mut(parent_id) {
            parent.set_activity(match (parent.activity(), child_status) {
                // A shared parent remains usable while shared children are
                // live, so ending one child must not destroy that fact (and
                // need not wait for sibling children to end).
                (LoanActivity::Active, _) => LoanActivity::Active,
                (LoanActivity::Suspended, ObligationStatus::Proven) => LoanActivity::Active,
                (LoanActivity::Suspended, _) => LoanActivity::Suspended,
                _ => LoanActivity::MaybeActive,
            });
        }
        debug_assert!(
            self.state
                .loan(child)
                .is_some_and(|loan| loan.activity() == LoanActivity::Ended)
        );
    }
}
