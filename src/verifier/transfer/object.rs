use super::*;

impl<'environment> TransferBuilder<'environment> {
    pub(super) fn allocate(
        &mut self,
        pointer_result: VirValue,
        permission_result: VirValue,
        size_value: VirValueId,
        alignment: u64,
        region: VirRegionId,
        element: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let size = word_fact(&self.state, size_value)?;
        let nonzero = if size.lower() > 0 {
            ObligationStatus::Proven
        } else if size.upper() == 0 {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::AllocationSizeNonZero { size },
            nonzero,
        );

        let within_limit = if size.upper() <= VIR_V0_MAX_ALLOCATION_BYTES {
            ObligationStatus::Proven
        } else if size.lower() > VIR_V0_MAX_ALLOCATION_BYTES {
            ObligationStatus::Refuted
        } else {
            ObligationStatus::Unknown
        };
        self.require(
            ResourceObligationKind::AllocationSizeWithinLimit {
                size,
                limit: VIR_V0_MAX_ALLOCATION_BYTES,
            },
            within_limit,
        );

        let exact = size.exact_value();
        self.require(
            ResourceObligationKind::AllocationExtentExact { size },
            if exact.is_some() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        );
        let allocation_id = AbstractAllocationId::vir_allocation_site(pointer_result.id);
        if let Some(size_bytes) =
            exact.filter(|size| *size > 0 && *size <= VIR_V0_MAX_ALLOCATION_BYTES)
        {
            let mut allocation = AbstractAllocation::new(region, size_bytes, alignment)?;
            let shape = self
                .memory
                .object_shape(element)
                .map_err(|_| TransferError::InvalidValidatedMemoryAccess(element))?;
            prepare_repeated_object_state(&mut allocation, &shape)?;
            allocation.seed_initialization_prefixes(self.memory, &shape);
            // Typed allocation creates empty storage authority, never a valid
            // pointee value. Resource absence is known independently of bytes.
            if shape.size_bytes() != 0 && size_bytes % shape.size_bytes() == 0 {
                for base in (0..size_bytes).step_by(shape.size_bytes() as usize) {
                    for leaf in shape.resource_leaves() {
                        let _ = allocation.set_resource_payload(
                            ResourcePayloadKey::new(
                                base + leaf.bytes().start_bytes(),
                                leaf.access(),
                            ),
                            MovePathState::Moved,
                        )?;
                    }
                }
            }
            if let Err(error) = self
                .state
                .introduce_allocation_instance(allocation_id, allocation)
            {
                self.instance_failure(error)?;
                self.define(
                    pointer_result,
                    AbstractValue::Pointer(unknown_pointer().with_memory_access(Some(element))),
                )?;
                return self.define(permission_result, unknown_value(VirType::Permission));
            }
            let range =
                ByteRange::new(0, size_bytes).map_err(|_| TransferError::InvalidDerivedRange)?;
            let alignment = GuaranteedAlignment::new(alignment)
                .map_err(|_| TransferError::InvalidValidatedAlignment(alignment))?;
            self.define(
                pointer_result,
                AbstractValue::Pointer(
                    AbstractPointer::new(
                        AbstractProvenance::Known(allocation_id),
                        U64Interval::exact(0),
                        alignment,
                    )
                    .with_memory_access(Some(element)),
                ),
            )?;
            self.define(
                permission_result,
                AbstractValue::Permission(AbstractPermission::new(
                    AbstractProvenance::Known(allocation_id),
                    AbstractByteRange::Exact(range),
                    AccessPermission::Write,
                    FreeCapability::Yes,
                )),
            )
        } else {
            self.define(
                pointer_result,
                AbstractValue::Pointer(unknown_pointer().with_memory_access(Some(element))),
            )?;
            self.define(permission_result, unknown_value(VirType::Permission))
        }
    }

    pub(super) fn local_storage(
        &mut self,
        pointer_result: VirValue,
        permission_result: VirValue,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let shape = self
            .memory
            .object_shape(access)
            .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
        let size_bytes = shape.size_bytes();
        let alignment_bytes = shape.alignment();
        let allocation_id = AbstractAllocationId::vir_local_storage_site(pointer_result.id);
        let mut allocation = AbstractAllocation::new_local(size_bytes, alignment_bytes)?;
        prepare_repeated_object_state(&mut allocation, &shape)?;
        allocation.seed_initialization_prefixes(self.memory, &shape);
        // Fresh variant-free storage has no payload. Keep this distinct from
        // Unknown so loop joins with a retired construction epoch stay empty.
        if shape.supports_resource_storage_reset() {
            for leaf in shape.resource_leaves() {
                let _ = allocation.set_resource_payload(
                    ResourcePayloadKey::new(leaf.bytes().start_bytes(), leaf.access()),
                    MovePathState::Moved,
                )?;
            }
        }
        if let Err(error) = self
            .state
            .introduce_allocation_instance(allocation_id, allocation)
        {
            self.instance_failure(error)?;
            self.define(
                pointer_result,
                AbstractValue::Pointer(unknown_pointer().with_memory_access(Some(access))),
            )?;
            return self.define(permission_result, unknown_value(VirType::Permission));
        }
        let range =
            ByteRange::new(0, size_bytes).map_err(|_| TransferError::InvalidDerivedRange)?;
        let alignment = GuaranteedAlignment::new(alignment_bytes)
            .map_err(|_| TransferError::InvalidValidatedAlignment(alignment_bytes))?;
        self.define(
            pointer_result,
            AbstractValue::Pointer(
                AbstractPointer::new(
                    AbstractProvenance::Known(allocation_id),
                    U64Interval::exact(0),
                    alignment,
                )
                .with_memory_access(Some(access)),
            ),
        )?;
        self.define(
            permission_result,
            AbstractValue::Permission(AbstractPermission::new(
                AbstractProvenance::Known(allocation_id),
                AbstractByteRange::Exact(range),
                AccessPermission::Write,
                FreeCapability::No,
            )),
        )
    }

    pub(super) fn active_variant_access_obligations(
        &mut self,
        pointer_id: VirValueId,
        pointer: AbstractPointer,
        allocation: &AbstractAllocation,
        access: VirMemoryAccess,
        access_bytes: u64,
    ) -> Result<(), TransferError> {
        let target = access_envelope(pointer.offset_bytes(), access_bytes);
        if !allocation.object_state().is_precise()
            && let AbstractProvenance::Known(allocation_id) = pointer.provenance()
        {
            self.require(
                ResourceObligationKind::ObjectStateWithinBudget {
                    allocation: allocation_id,
                },
                ObligationStatus::Unknown,
            );
        }
        for (key, active) in allocation.object_state().active_variants() {
            let shape = self
                .memory
                .object_shape(key.access())
                .map_err(|_| TransferError::InvalidValidatedMemoryAccess(key.access()))?;
            let mut allowed = BTreeSet::new();
            let mut related = false;
            for variant in shape
                .variants()
                .iter()
                .filter(|variant| variant.path().segments().is_empty())
            {
                for leaf in variant
                    .leaves()
                    .iter()
                    .filter(|leaf| leaf.access() == access)
                {
                    let Some(start) = key.offset_bytes().checked_add(leaf.bytes().start_bytes())
                    else {
                        continue;
                    };
                    let Some(end) = key.offset_bytes().checked_add(leaf.bytes().end_bytes()) else {
                        continue;
                    };
                    let leaf_range = ByteRange::new(start, end)
                        .map_err(|_| TransferError::InvalidDerivedRange)?;
                    if target.is_some_and(|target| target.overlaps(leaf_range)) {
                        related = true;
                    }
                    if pointer.offset_bytes().exact_value().is_some_and(|offset| {
                        offset == leaf_range.start() && access_bytes == leaf_range.length()
                    }) {
                        allowed.insert(variant.variant());
                    }
                }
            }
            if !related {
                continue;
            }
            let status = if pointer.offset_bytes().exact_value().is_none() || allowed.is_empty() {
                ObligationStatus::Unknown
            } else {
                active_variant_allows_access(active, &allowed)
            };
            self.require(
                ResourceObligationKind::ActiveVariantAllowsAccess {
                    pointer: pointer_id,
                    enum_access: key.access(),
                    enum_offset_bytes: key.offset_bytes(),
                },
                status,
            );
        }
        Ok(())
    }

    pub(super) fn resource_initialize(
        &mut self,
        destination_id: VirValueId,
        destination_permission_id: VirValueId,
        value_id: VirValueId,
        value_permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let resource = storable_resource(self.memory, access)?;
        let pointee_access = resource.pointee();
        let destination = pointer_fact(&self.state, destination_id)?;
        let value = pointer_fact(&self.state, value_id)?;
        let value_permission = permission_fact(&self.state, value_permission_id)?;

        self.require(
            ResourceObligationKind::PointerMemoryAccessMatches {
                pointer: value_id,
                expected: pointee_access,
                found: value.memory_access(),
            },
            memory_access_status(value.memory_access(), pointee_access),
        );
        let reference_status = match resource {
            StorableResource::Own { .. } => {
                self.require_owner_payload_obligations(
                    value_id,
                    value_permission_id,
                    value,
                    value_permission,
                );
                None
            }
            StorableResource::Reference { kind, .. } => {
                let (loan, status) = permission_loan_access_status(
                    &self.state,
                    value_permission_id,
                    value_permission,
                    LoanAccess::bytes(
                        value,
                        self.memory
                            .object_shape(pointee_access)
                            .map_err(|_| TransferError::InvalidDerivedRange)?
                            .size_bytes(),
                        loan_access(kind),
                    ),
                    self.relation_limits,
                    &self.relations,
                );
                self.require(
                    ResourceObligationKind::LoanCompatible {
                        loan,
                        permission: value_permission_id,
                        access: pointer_access_range(self.memory, value, pointee_access),
                        required: loan_access(kind),
                    },
                    status,
                );
                Some((loan, status))
            }
        };
        self.memory_access(
            destination_id,
            destination_permission_id,
            AccessPermission::Write,
            InitializationRequirement::Uninitialized,
            MemoryEffect::WriteValue,
            access,
        )?;

        let destination_offset = destination.offset_bytes().exact_value();
        self.require(
            ResourceObligationKind::ResourcePayloadLocationExact {
                pointer: destination_id,
                access,
            },
            if destination_offset.is_some() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        );
        if let (AbstractProvenance::Known(allocation_id), Some(offset)) =
            (destination.provenance(), destination_offset)
        {
            let key = ResourcePayloadKey::new(offset, access);
            let exact_reference =
                reference_status.is_none_or(|(loan, status)| loan.is_some() && status.is_proven());
            let permission = value_permission
                .with_availability(PermissionAvailability::Available)
                .with_authority(if exact_reference {
                    value_permission.authority()
                } else {
                    PermissionAuthority::Unknown
                });
            if let Some(allocation) = self.state.allocation_mut(allocation_id) {
                let _ = allocation.set_resource_payload(
                    key,
                    MovePathState::available(TypedResourcePayload::new(value, permission)),
                )?;
            }
            if let Some((Some(loan_id), status)) = reference_status
                && let Some(loan) = self.state.loan_mut(loan_id)
            {
                if status.is_proven()
                    && loan.move_authority_to_storage(value_permission_id, allocation_id, key)
                {
                    // The authority now lives in the typed object payload.
                } else {
                    loan.set_activity(LoanActivity::MaybeActive);
                }
            }
        }
        mark_permission_consumed(&mut self.state, value_permission_id)
    }

    pub(super) fn resource_take(
        &mut self,
        pointer_result: VirValue,
        permission_result: VirValue,
        source_id: VirValueId,
        source_permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let resource = storable_resource(self.memory, access)?;
        let pointee_access = resource.pointee();
        let source = pointer_fact(&self.state, source_id)?;
        self.memory_access(
            source_id,
            source_permission_id,
            AccessPermission::Write,
            InitializationRequirement::Initialized,
            MemoryEffect::None,
            access,
        )?;

        let allocation_id = match source.provenance() {
            AbstractProvenance::Known(allocation) => Some(allocation),
            AbstractProvenance::Unknown => None,
        };
        let offset = source.offset_bytes().exact_value();
        self.require(
            ResourceObligationKind::ResourcePayloadLocationExact {
                pointer: source_id,
                access,
            },
            if offset.is_some() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        );
        let payload_state = allocation_id
            .zip(offset)
            .and_then(|(allocation, offset)| {
                self.state.allocation(allocation).map(|allocation| {
                    allocation.resource_payload(ResourcePayloadKey::new(offset, access))
                })
            })
            .unwrap_or(MovePathState::Unknown);
        self.require(
            ResourceObligationKind::ResourcePayloadAvailable {
                allocation: allocation_id,
                offset_bytes: offset,
                access,
            },
            move_path_availability_status(&payload_state),
        );

        let (pointer, mut permission) = match payload_state {
            MovePathState::Available(payload) => (payload.pointer(), payload.permission()),
            MovePathState::Moved | MovePathState::Unknown => (
                unknown_pointer().with_memory_access(Some(pointee_access)),
                fresh_unknown_permission(),
            ),
        };
        let key = offset.map(|offset| ResourcePayloadKey::new(offset, access));
        if let StorableResource::Reference { kind, .. } = resource {
            let (loan_id, status) = match (allocation_id, key, permission.authority()) {
                (Some(allocation), Some(key), PermissionAuthority::Loan(loan_id)) => {
                    let status =
                        self.state
                            .loan(loan_id)
                            .map_or(ObligationStatus::Unknown, |loan| {
                                combine_statuses([
                                    stored_loan_authority_status(
                                        loan, allocation, key, loan_id, kind,
                                    ),
                                    loan_activity_access_status(loan.activity()),
                                    loan_authority_access_status_for_payload(
                                        loan,
                                        pointer,
                                        self.memory
                                            .layout(pointee_access.layout)
                                            .map(|layout| layout.size_bytes),
                                        loan_access(kind),
                                    ),
                                ])
                            });
                    (Some(loan_id), status)
                }
                (_, _, PermissionAuthority::Owner | PermissionAuthority::Loan(_)) => {
                    (None, ObligationStatus::Refuted)
                }
                (_, _, PermissionAuthority::Unknown) => (None, ObligationStatus::Unknown),
            };
            self.require(
                ResourceObligationKind::LoanCompatible {
                    loan: loan_id,
                    permission: permission_result.id,
                    access: pointer_access_range(self.memory, pointer, pointee_access),
                    required: loan_access(kind),
                },
                status,
            );
            if let (Some(loan_id), Some(allocation), Some(key)) = (loan_id, allocation_id, key)
                && let Some(loan) = self.state.loan_mut(loan_id)
            {
                if status.is_proven()
                    && loan.move_authority_from_storage(allocation, key, permission_result.id)
                {
                    permission = permission.with_authority(PermissionAuthority::Loan(loan_id));
                } else {
                    permission = permission.with_authority(PermissionAuthority::Unknown);
                    loan.set_activity(LoanActivity::MaybeActive);
                }
            } else {
                permission = permission.with_authority(PermissionAuthority::Unknown);
            }
        }
        self.define(pointer_result, AbstractValue::Pointer(pointer))?;
        self.define(permission_result, AbstractValue::Permission(permission))?;

        if let (Some(allocation_id), Some(offset)) = (allocation_id, offset)
            && let Some(allocation) = self.state.allocation_mut(allocation_id)
        {
            let width = self
                .memory
                .layout(access.layout)
                .ok_or(TransferError::InvalidValidatedMemoryAccess(access))?
                .size_bytes;
            let range = ByteRange::from_start_and_length(offset, width)
                .map_err(|_| TransferError::InvalidDerivedRange)?;
            allocation.mark_uninitialized(range)?;
            let _ = allocation.set_resource_payload(
                ResourcePayloadKey::new(offset, access),
                MovePathState::Moved,
            )?;
        }
        Ok(())
    }

    pub(super) fn require_owner_payload_obligations(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        pointer: AbstractPointer,
        permission: AbstractPermission,
    ) {
        self.require(
            ResourceObligationKind::PointerProvenanceKnown {
                pointer: pointer_id,
            },
            known_provenance_status(pointer.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerAtAllocationBase {
                pointer: pointer_id,
            },
            base_pointer_status(pointer.offset_bytes()),
        );
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: permission_id,
            },
            permission_availability_status(permission.availability()),
        );
        self.require(
            ResourceObligationKind::PermissionCanFree {
                permission: permission_id,
            },
            free_capability_status(permission.free_capability()),
        );
        let full_access = match pointer.provenance() {
            AbstractProvenance::Known(allocation) => self
                .state
                .allocation(allocation)
                .and_then(|allocation| ByteRange::new(0, allocation.size_bytes()).ok()),
            AbstractProvenance::Unknown => None,
        };
        let (loan, loan_status) = permission_loan_access_status(
            &self.state,
            permission_id,
            permission,
            LoanAccess::whole(pointer, full_access, AccessPermission::Write),
            self.relation_limits,
            &self.relations,
        );
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan,
                permission: permission_id,
                access: full_access,
                required: AccessPermission::Write,
            },
            loan_status,
        );
        if let AbstractProvenance::Known(allocation_id) = pointer.provenance() {
            let allocation = self.state.allocation(allocation_id).cloned();
            self.require(
                ResourceObligationKind::AllocationTracked {
                    allocation: allocation_id,
                },
                if allocation.is_some() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
            self.require(
                ResourceObligationKind::PermissionMatchesAllocation {
                    permission: permission_id,
                    allocation: allocation_id,
                },
                provenance_match_status(permission.provenance(), allocation_id),
            );
            if let Some(allocation) = allocation {
                self.require(
                    ResourceObligationKind::AllocationLive {
                        allocation: allocation_id,
                    },
                    liveness_status(allocation.liveness()),
                );
                self.require(
                    ResourceObligationKind::AllocationOwned {
                        allocation: allocation_id,
                    },
                    ownership_status(allocation.ownership()),
                );
                self.require(
                    ResourceObligationKind::PermissionCoversAllocation {
                        permission: permission_id,
                        allocation: allocation_id,
                    },
                    full_permission_status(permission.range(), allocation.size_bytes()),
                );
            }
        }
    }

    pub(super) fn object_transfer(
        &mut self,
        effect: ObjectTransferEffect,
    ) -> Result<(), TransferError> {
        let destination = self.object_access_facts(
            effect.destination,
            effect.destination_permission,
            effect.access,
            AccessPermission::Write,
        )?;
        let source = self.object_access_facts(
            effect.source,
            effect.source_permission,
            effect.access,
            if matches!(effect.source_mode, VirObjectSourceMode::Move) {
                AccessPermission::Write
            } else {
                AccessPermission::Read
            },
        )?;

        self.require(
            ResourceObligationKind::ObjectNonOverlapping {
                destination: effect.destination,
                source: effect.source,
                size_bytes: source.shape.size_bytes(),
            },
            self.relations.queries.non_overlapping(
                &self.state,
                destination.pointer,
                source.pointer,
                source.shape.size_bytes(),
                self.relation_limits,
            ),
        );
        match effect.source_mode {
            VirObjectSourceMode::Copy => self.require(
                ResourceObligationKind::ObjectTriviallyCopyable {
                    access: effect.access,
                },
                copyable_object_status(self.memory, effect.access),
            ),
            VirObjectSourceMode::Move => self.require(
                ResourceObligationKind::ObjectMoveSupported {
                    access: effect.access,
                },
                movable_object_status(self.memory, &source.shape),
            ),
        }

        let source_mask = active_object_mask(&source);
        self.require_active_variants(&source, &source_mask);
        self.require_object_initialization(
            &source,
            &source_mask.possible_value_bytes,
            InitializationRequirement::Initialized,
        );
        self.require_object_validity(&source, &source_mask.possible_value_bytes);
        self.require_object_resource_payloads(&source, &source_mask);

        let destination_mask = active_object_mask(&destination);
        match effect.destination_mode {
            VirObjectDestinationMode::Initialize => self.require_object_initialization(
                &destination,
                &source_mask.possible_value_bytes,
                InitializationRequirement::Uninitialized,
            ),
            VirObjectDestinationMode::Replace => {
                self.require_active_variants(&destination, &destination_mask);
                self.require_object_initialization(
                    &destination,
                    &destination_mask.possible_value_bytes,
                    InitializationRequirement::Initialized,
                );
                self.require_object_validity(&destination, &destination_mask.possible_value_bytes);
                self.require(
                    ResourceObligationKind::ObjectTriviallyDroppable {
                        access: effect.access,
                    },
                    droppable_object_status(self.memory, effect.access),
                );
            }
        }

        let overwritten_destination =
            if matches!(effect.destination_mode, VirObjectDestinationMode::Replace) {
                source_mask
                    .possible_value_bytes
                    .union(&destination_mask.possible_value_bytes)
            } else {
                source_mask.possible_value_bytes.clone()
            };
        let preserves_complete_value_state =
            matches!(effect.destination_mode, VirObjectDestinationMode::Replace)
                && source_mask.possible_value_bytes == source_mask.guaranteed_value_bytes
                && destination_mask.possible_value_bytes == destination_mask.guaranteed_value_bytes
                && source_mask.possible_value_bytes == destination_mask.possible_value_bytes;
        // A complete trivial replacement preserves initialization and validity
        // even when the destination offset is an interval: every possible
        // selected object was required to be valid before the operation and
        // receives a complete valid value. Forgetting the entire offset
        // envelope here would lose facts about unaffected array elements.
        if !preserves_complete_value_state {
            self.apply_object_write(
                &destination,
                &overwritten_destination,
                &source_mask.guaranteed_value_bytes,
            )?;
        }
        if matches!(effect.destination_mode, VirObjectDestinationMode::Replace)
            && destination_mask.guaranteed_value_bytes.is_precise()
            && source_mask.possible_value_bytes.is_precise()
        {
            let mut retired = destination_mask.guaranteed_value_bytes.clone();
            for range in source_mask.possible_value_bytes.ranges() {
                retired.remove(*range);
            }
            self.apply_object_uninitialized(&destination, &retired)?;
        }
        self.copy_active_variants(&source, &destination, &source_mask)?;
        // Representation cache invalidation must not forget independently
        // known empty payload slots (notably inactive enum variants).
        if let (Some(id), Some(previous)) = (destination.allocation_id, &destination.allocation)
            && let Some(allocation) = self.state.allocation_mut(id)
        {
            restore_empty_resource_paths(allocation, &empty_resource_paths(previous))?;
        }
        self.transfer_object_resource_payloads(
            &source,
            &destination,
            &source_mask,
            effect.source_mode,
        )?;
        if matches!(effect.source_mode, VirObjectSourceMode::Move) {
            self.apply_object_deinitialize(&source, &source_mask)?;
        }
        Ok(())
    }

    pub(super) fn require_object_resource_payloads(
        &mut self,
        object: &ObjectAccessFacts,
        mask: &ActiveObjectMask,
    ) {
        let base = object.pointer.offset_bytes().exact_value();
        for leaf in &mask.possible_resource_leaves {
            let offset = base.and_then(|base| base.checked_add(leaf.bytes().start_bytes()));
            let state = object
                .allocation
                .as_ref()
                .zip(offset)
                .map(|(allocation, offset)| {
                    allocation.resource_payload(ResourcePayloadKey::new(offset, leaf.access()))
                })
                .unwrap_or(MovePathState::Unknown);
            let guaranteed = mask
                .guaranteed_resource_leaves
                .iter()
                .any(|candidate| candidate == leaf);
            let availability = if guaranteed {
                match (&state, leaf.kind()) {
                    (MovePathState::Available(payload), VirPointerKind::Reference) => {
                        let PermissionAuthority::Loan(loan_id) = payload.permission().authority()
                        else {
                            self.require(
                                ResourceObligationKind::ResourcePayloadAvailable {
                                    allocation: object.allocation_id,
                                    offset_bytes: offset,
                                    access: leaf.access(),
                                },
                                ObligationStatus::Refuted,
                            );
                            continue;
                        };
                        object.allocation_id.zip(offset).map_or(
                            ObligationStatus::Unknown,
                            |(allocation, offset)| {
                                let key = ResourcePayloadKey::new(offset, leaf.access());
                                self.state
                                    .loan(loan_id)
                                    .map_or(ObligationStatus::Unknown, |loan| {
                                        combine_statuses([
                                            stored_loan_authority_status(
                                                loan,
                                                allocation,
                                                key,
                                                loan_id,
                                                if leaf.mutability() == VirMutability::Const {
                                                    VirLoanKind::Shared
                                                } else {
                                                    VirLoanKind::Mutable
                                                },
                                            ),
                                            loan_activity_access_status(loan.activity()),
                                            loan_authority_access_status_for_payload(
                                                loan,
                                                payload.pointer(),
                                                reference_pointee(self.memory, leaf.access())
                                                    .ok()
                                                    .and_then(|pointee| {
                                                        self.memory
                                                            .layout(pointee.layout)
                                                            .map(|layout| layout.size_bytes)
                                                    }),
                                                if leaf.mutability() == VirMutability::Const {
                                                    AccessPermission::Read
                                                } else {
                                                    AccessPermission::Write
                                                },
                                            ),
                                        ])
                                    })
                            },
                        )
                    }
                    (MovePathState::Available(_), VirPointerKind::Own) => ObligationStatus::Proven,
                    (MovePathState::Available(_), VirPointerKind::Raw) => ObligationStatus::Refuted,
                    (MovePathState::Moved, _) => ObligationStatus::Refuted,
                    (MovePathState::Unknown, _) => ObligationStatus::Unknown,
                }
            } else {
                ObligationStatus::Unknown
            };
            self.require(
                ResourceObligationKind::ResourcePayloadAvailable {
                    allocation: object.allocation_id,
                    offset_bytes: offset,
                    access: leaf.access(),
                },
                availability,
            );
        }
    }

    pub(super) fn transfer_object_resource_payloads(
        &mut self,
        source: &ObjectAccessFacts,
        destination: &ObjectAccessFacts,
        mask: &ActiveObjectMask,
        source_mode: VirObjectSourceMode,
    ) -> Result<(), TransferError> {
        let (Some(source_id), Some(source_base), Some(destination_id), Some(destination_base)) = (
            source.allocation_id,
            source.pointer.offset_bytes().exact_value(),
            destination.allocation_id,
            destination.pointer.offset_bytes().exact_value(),
        ) else {
            return Ok(());
        };
        let payloads = mask
            .guaranteed_resource_leaves
            .iter()
            .filter_map(|leaf| {
                let source_offset = source_base.checked_add(leaf.bytes().start_bytes())?;
                let state = self
                    .state
                    .allocation(source_id)?
                    .resource_payload(ResourcePayloadKey::new(source_offset, leaf.access()));
                let MovePathState::Available(payload) = state else {
                    return None;
                };
                let destination_offset =
                    destination_base.checked_add(leaf.bytes().start_bytes())?;
                Some((
                    leaf.clone(),
                    ResourcePayloadKey::new(source_offset, leaf.access()),
                    ResourcePayloadKey::new(destination_offset, leaf.access()),
                    payload,
                ))
            })
            .collect::<Vec<_>>();
        for (leaf, source_key, destination_key, payload) in &payloads {
            if leaf.kind() != VirPointerKind::Reference {
                continue;
            }
            let PermissionAuthority::Loan(loan_id) = payload.permission().authority() else {
                continue;
            };
            match source_mode {
                VirObjectSourceMode::Move => {
                    if let Some(loan) = self.state.loan_mut(loan_id)
                        && !loan.move_stored_authority(
                            source_id,
                            *source_key,
                            destination_id,
                            *destination_key,
                        )
                    {
                        loan.set_activity(LoanActivity::MaybeActive);
                    }
                }
                VirObjectSourceMode::Copy => {
                    let context = self
                        .loan_context
                        .ok_or(TransferError::MissingLoanTransferContext)?;
                    let alias_status = self.require_alias_budget(loan_id, context.limits);
                    if alias_status.is_proven()
                        && let Some(loan) = self.state.loan_mut(loan_id)
                    {
                        loan.add_stored_authority(destination_id, *destination_key);
                    } else if let Some(loan) = self.state.loan_mut(loan_id) {
                        loan.set_activity(LoanActivity::MaybeActive);
                    }
                }
            }
        }
        if let Some(allocation) = self.state.allocation_mut(destination_id) {
            for (_, _, key, payload) in payloads {
                let _ = allocation.set_resource_payload(key, MovePathState::Available(payload))?;
            }
        }
        Ok(())
    }

    pub(super) fn resource_storage_reset(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Write)?;
        let mask = active_object_mask(&object);
        let mut resources = ByteSet::new();
        for leaf in &mask.possible_resource_leaves {
            resources.insert(object_relative_range(leaf.bytes())?);
        }
        self.require_object_initialization(
            &object,
            &resources,
            InitializationRequirement::Uninitialized,
        );
        let Some(allocation_id) = object.allocation_id else {
            return Ok(());
        };
        let status = object.allocation.as_ref().map_or(
            ObligationStatus::Unknown,
            allocation_resource_payload_empty_status,
        );
        self.require(
            ResourceObligationKind::AllocationResourcePayloadEmpty {
                allocation: allocation_id,
            },
            status,
        );
        if !status.is_proven() {
            return Ok(());
        }
        self.apply_object_deinitialize(&object, &mask)?;
        if let Some(base) = object.pointer.offset_bytes().exact_value()
            && let Some(allocation) = self.state.allocation_mut(allocation_id)
        {
            for leaf in object.shape.resource_leaves() {
                if let Some(end) = base.checked_add(leaf.bytes().end_bytes())
                    && end <= allocation.size_bytes()
                {
                    let key =
                        ResourcePayloadKey::new(base + leaf.bytes().start_bytes(), leaf.access());
                    let _ = allocation.set_resource_payload(key, MovePathState::Moved)?;
                }
            }
        }
        Ok(())
    }

    pub(super) fn object_deinitialize(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Write)?;
        let mask = active_object_mask(&object);
        self.require_active_variants(&object, &mask);
        self.require_object_initialization(
            &object,
            &mask.possible_value_bytes,
            InitializationRequirement::Initialized,
        );
        self.require_object_validity(&object, &mask.possible_value_bytes);
        self.require(
            ResourceObligationKind::ObjectTriviallyDroppable { access },
            droppable_object_status(self.memory, access),
        );
        self.apply_object_deinitialize(&object, &mask)
    }

    pub(super) fn object_drop(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
        condition_id: VirValueId,
    ) -> Result<(), TransferError> {
        match self.require_drop_flag(condition_id)? {
            Some(true) => {}
            Some(false) | None => return Ok(()),
        }
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Write)?;
        let mask = active_object_mask(&object);
        self.require(
            ResourceObligationKind::ObjectBuiltinDroppable { access },
            builtin_droppable_object_status(self.memory, access),
        );

        // Fresh or wholly moved tagged storage has no representation to decode.
        // Retirement is safe only with independently proven byte and payload
        // absence over the whole object; Unknown is never an empty value.
        if !mask.sites.is_empty()
            && let Some(empty_bytes) = empty_tagged_storage(&object, self.memory)
        {
            self.require_object_initialization(
                &object,
                &empty_bytes,
                InitializationRequirement::Uninitialized,
            );
            self.require(
                ResourceObligationKind::ObjectResourcePayloadEmpty {
                    allocation: object.allocation_id,
                    offset_bytes: object.pointer.offset_bytes().exact_value(),
                    access,
                },
                object_resource_payload_empty_status(&object, self.memory),
            );
            return Ok(());
        }
        self.require_active_variants(&object, &mask);

        // Cleanup observes representation tags and present resource payloads,
        // not trivial payload bytes. In particular, moving an aggregate field
        // out of an enum may retire those bytes without retiring the root tag.
        let mut tags = ByteSet::new();
        for (site, _, _) in &mask.sites {
            tags.insert(site.tag);
        }
        if !tags.is_empty() {
            self.require_object_initialization(
                &object,
                &tags,
                InitializationRequirement::Initialized,
            );
            self.require_object_validity(&object, &tags);
        }

        let base = object.pointer.offset_bytes().exact_value();
        let mut dropped = Vec::new();
        for leaf in &mask.possible_resource_leaves {
            let offset = base.and_then(|base| base.checked_add(leaf.bytes().start_bytes()));
            let state = object
                .allocation
                .as_ref()
                .zip(offset)
                .map(|(allocation, offset)| {
                    allocation.resource_payload(ResourcePayloadKey::new(offset, leaf.access()))
                })
                .unwrap_or(MovePathState::Unknown);
            let guaranteed = mask
                .guaranteed_resource_leaves
                .iter()
                .any(|candidate| candidate == leaf);
            let status = match state {
                MovePathState::Available(ref payload) if guaranteed => match leaf.kind() {
                    VirPointerKind::Own => object_drop_payload_status(&self.state, payload),
                    VirPointerKind::Reference => {
                        let PermissionAuthority::Loan(loan_id) = payload.permission().authority()
                        else {
                            self.require(
                                ResourceObligationKind::ObjectDropPayloadValid {
                                    allocation: object.allocation_id,
                                    offset_bytes: offset,
                                    access: leaf.access(),
                                },
                                ObligationStatus::Refuted,
                            );
                            continue;
                        };
                        object.allocation_id.zip(offset).map_or(
                            ObligationStatus::Unknown,
                            |(allocation, offset)| {
                                let key = ResourcePayloadKey::new(offset, leaf.access());
                                self.state
                                    .loan(loan_id)
                                    .map_or(ObligationStatus::Unknown, |loan| {
                                        combine_statuses([
                                            stored_loan_authority_status(
                                                loan,
                                                allocation,
                                                key,
                                                loan_id,
                                                if leaf.mutability() == VirMutability::Const {
                                                    VirLoanKind::Shared
                                                } else {
                                                    VirLoanKind::Mutable
                                                },
                                            ),
                                            loan_activity_access_status(loan.activity()),
                                            no_active_child_status(&self.state, loan_id),
                                        ])
                                    })
                            },
                        )
                    }
                    VirPointerKind::Raw => ObligationStatus::Refuted,
                },
                MovePathState::Moved if guaranteed => ObligationStatus::Proven,
                MovePathState::Available(_) | MovePathState::Moved | MovePathState::Unknown => {
                    ObligationStatus::Unknown
                }
            };
            self.require(
                ResourceObligationKind::ObjectDropPayloadValid {
                    allocation: object.allocation_id,
                    offset_bytes: offset,
                    access: leaf.access(),
                },
                status,
            );
            if let (MovePathState::Available(payload), Some(owner), Some(offset)) =
                (state, object.allocation_id, offset)
            {
                dropped.push((
                    owner,
                    ResourcePayloadKey::new(offset, leaf.access()),
                    leaf.kind(),
                    payload,
                    status,
                ));
            }
        }

        for (owner, key, kind, payload, status) in dropped {
            if status.is_proven() {
                match kind {
                    VirPointerKind::Own => {
                        if let AbstractProvenance::Known(allocation) =
                            payload.pointer().provenance()
                            && let Some(allocation) = self.state.allocation_mut(allocation)
                        {
                            allocation.mark_dead();
                        }
                    }
                    VirPointerKind::Reference => {
                        if let PermissionAuthority::Loan(loan_id) = payload.permission().authority()
                        {
                            self.end_stored_loan_authority(loan_id, owner, key);
                        }
                    }
                    VirPointerKind::Raw => {}
                }
                if let Some(allocation) = self.state.allocation_mut(owner) {
                    let _ = allocation.set_resource_payload(key, MovePathState::Moved)?;
                }
            }
        }
        self.apply_object_deinitialize(&object, &mask)
    }

    pub(super) fn drop_own(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        condition_id: VirValueId,
    ) -> Result<(), TransferError> {
        match self.require_drop_flag(condition_id)? {
            Some(true) => self.free(pointer_id, permission_id),
            Some(false) | None => Ok(()),
        }
    }

    pub(super) fn require_drop_flag(
        &mut self,
        condition_id: VirValueId,
    ) -> Result<Option<bool>, TransferError> {
        let condition = bool_fact(&self.state, condition_id)?;
        let value = match condition {
            AbstractBool::True => Some(true),
            AbstractBool::False => Some(false),
            AbstractBool::Unknown => None,
        };
        self.require(
            ResourceObligationKind::DropFlagKnown {
                condition: condition_id,
            },
            if value.is_some() {
                ObligationStatus::Proven
            } else {
                ObligationStatus::Unknown
            },
        );
        Ok(value)
    }

    pub(super) fn enum_set_discriminant(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
        variant: VirVariantId,
        mode: VirObjectDestinationMode,
    ) -> Result<(), TransferError> {
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Write)?;
        let case = object
            .shape
            .variants()
            .iter()
            .find(|case| case.path().segments().is_empty() && case.variant() == variant)
            .ok_or(TransferError::InvalidValidatedEnumVariant { access, variant })?;
        let tag = ByteSet::single(object_relative_range(case.tag())?);
        // Changing representation must not erase a live payload, even when a
        // malformed producer has already forgotten or overwritten its tag.
        let empty = object_resource_payload_empty_status(&object, self.memory);
        self.require(
            ResourceObligationKind::ObjectResourcePayloadEmpty {
                allocation: object.allocation_id,
                offset_bytes: object.pointer.offset_bytes().exact_value(),
                access,
            },
            empty,
        );
        if !empty.is_proven() {
            return Ok(());
        }
        let previous_mask = match mode {
            VirObjectDestinationMode::Initialize => None,
            VirObjectDestinationMode::Replace => Some(active_object_mask(&object)),
        };

        match mode {
            VirObjectDestinationMode::Initialize => self.require_object_initialization(
                &object,
                &tag,
                InitializationRequirement::Uninitialized,
            ),
            VirObjectDestinationMode::Replace => {
                let mask = previous_mask.as_ref().expect("replace mask is present");
                self.require_active_variants(&object, mask);
                self.require_object_initialization(
                    &object,
                    &tag,
                    InitializationRequirement::Initialized,
                );
                self.require_object_validity(&object, &tag);
                self.require(
                    ResourceObligationKind::ObjectTriviallyDroppable { access },
                    droppable_object_status(self.memory, access),
                );
            }
        }

        let mut retired_payload = ByteSet::new();
        for range in case.value_bytes() {
            retired_payload.insert(object_relative_range(*range)?);
        }
        if let Some(mask) = previous_mask {
            retired_payload = retired_payload.union(&mask.possible_value_bytes);
        }
        for range in tag.ranges() {
            retired_payload.remove(*range);
        }
        self.apply_object_uninitialized(&object, &retired_payload)?;
        self.apply_object_write(&object, &tag, &tag)?;
        if let (Some(allocation_id), Some(base)) = (
            object.allocation_id,
            object.pointer.offset_bytes().exact_value(),
        ) && let Some(allocation) = self.state.allocation_mut(allocation_id)
        {
            if let Some(envelope) = object.envelope {
                allocation.forget_object_state(envelope)?;
            }
            let tracked = allocation.set_active_variant(
                ObjectStateKey::new(base, access),
                ActiveVariantState::Exact(variant),
            )?;
            if !tracked {
                // The effect remains safe, but later active-variant queries
                // must observe Unknown once the precision budget is exhausted.
            }
            // These are empty construction slots, not initialized values or
            // resource authority. Whole observation still checks every active
            // value byte and payload independently.
            for leaf in object.shape.resource_leaves() {
                let _ = allocation.set_resource_payload(
                    ResourcePayloadKey::new(base + leaf.bytes().start_bytes(), leaf.access()),
                    MovePathState::Moved,
                )?;
            }
        }
        Ok(())
    }

    pub(super) fn enum_discriminant(
        &mut self,
        result: VirValue,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let object =
            self.object_access_facts(pointer_id, permission_id, access, AccessPermission::Read)?;
        let root_cases = object
            .shape
            .variants()
            .iter()
            .filter(|case| case.path().segments().is_empty() && case.enum_access() == access)
            .collect::<Vec<_>>();
        let first = root_cases
            .first()
            .copied()
            .ok_or(TransferError::InvalidValidatedMemoryAccess(access))?;
        let tag = ByteSet::single(object_relative_range(first.tag())?);
        if root_cases.iter().any(|case| case.tag() != first.tag()) {
            return Err(TransferError::InvalidValidatedMemoryAccess(access));
        }
        self.require_object_initialization(&object, &tag, InitializationRequirement::Initialized);
        self.require_object_validity(&object, &tag);

        let declared = root_cases
            .iter()
            .map(|case| case.variant())
            .collect::<BTreeSet<_>>();
        let mut possible = object
            .pointer
            .offset_bytes()
            .exact_value()
            .zip(object.allocation.as_ref())
            .and_then(|(base, allocation)| {
                allocation
                    .active_variant(ObjectStateKey::new(base, access))
                    .alternatives()
            })
            .unwrap_or_else(|| declared.clone());
        possible.retain(|variant| declared.contains(variant));
        if possible.is_empty() {
            possible = declared;
        }
        let active = if possible.len() == 1 {
            ActiveVariantState::Exact(*possible.first().expect("one possible variant"))
        } else {
            ActiveVariantState::Alternatives(possible.clone())
        };
        if let (Some(allocation_id), Some(base)) = (
            object.allocation_id,
            object.pointer.offset_bytes().exact_value(),
        ) && let Some(allocation) = self.state.allocation_mut(allocation_id)
        {
            let _ = allocation.set_active_variant(ObjectStateKey::new(base, access), active)?;
        }
        let mut discriminants = root_cases
            .iter()
            .filter(|case| possible.contains(&case.variant()))
            .map(|case| case.discriminant());
        let first_discriminant = discriminants
            .next()
            .ok_or(TransferError::InvalidValidatedMemoryAccess(access))?;
        let (lower, upper) = discriminants.fold(
            (first_discriminant, first_discriminant),
            |(lower, upper), value| (lower.min(value), upper.max(value)),
        );
        let interval = U64Interval::new(lower, upper)
            .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
        self.define(
            result,
            AbstractValue::EnumDiscriminant(EnumDiscriminantFact::new(
                interval,
                object.pointer,
                access,
            )),
        )
    }

    pub(super) fn require_active_variants(
        &mut self,
        object: &ObjectAccessFacts,
        mask: &ActiveObjectMask,
    ) {
        for (site, _, status) in &mask.sites {
            self.require(
                ResourceObligationKind::ObjectActiveVariantKnown {
                    allocation: object.allocation_id,
                    offset_bytes: object
                        .pointer
                        .offset_bytes()
                        .exact_value()
                        .and_then(|base| base.checked_add(site.offset_bytes)),
                    access: site.access,
                },
                *status,
            );
        }
    }

    pub(super) fn require_object_initialization(
        &mut self,
        object: &ObjectAccessFacts,
        relative_ranges: &ByteSet,
        requirement: InitializationRequirement,
    ) {
        let mut status =
            object
                .allocation
                .as_ref()
                .map_or(ObligationStatus::Unknown, |allocation| {
                    object_ranges_status(object.pointer, relative_ranges, |range| {
                        initialization_status(
                            allocation.initialization().classify(range),
                            requirement,
                        )
                    })
                });
        if matches!(requirement, InitializationRequirement::Initialized)
            && !status.is_proven()
            && self.object_prefix_covers(object)
        {
            status = ObligationStatus::Proven;
        }
        let kind = match requirement {
            InitializationRequirement::Initialized => {
                ResourceObligationKind::ObjectValueBytesInitialized {
                    allocation: object.allocation_id,
                    access: object.envelope,
                    object: object.shape.access(),
                }
            }
            InitializationRequirement::Uninitialized => {
                ResourceObligationKind::ObjectValueBytesUninitialized {
                    allocation: object.allocation_id,
                    access: object.envelope,
                    object: object.shape.access(),
                }
            }
            InitializationRequirement::None => return,
        };
        self.require(kind, status);
    }

    pub(super) fn require_object_validity(
        &mut self,
        object: &ObjectAccessFacts,
        relative_ranges: &ByteSet,
    ) {
        let mut status =
            object
                .allocation
                .as_ref()
                .map_or(ObligationStatus::Unknown, |allocation| {
                    object_ranges_status(object.pointer, relative_ranges, |range| {
                        if allocation.valid_value_bytes().contains(range) {
                            ObligationStatus::Proven
                        } else {
                            ObligationStatus::Unknown
                        }
                    })
                });
        if !status.is_proven() && self.object_prefix_covers(object) {
            status = ObligationStatus::Proven;
        }
        self.require(
            ResourceObligationKind::ObjectRepresentationValid {
                allocation: object.allocation_id,
                access: object.envelope,
                object: object.shape.access(),
            },
            status,
        );
    }

    pub(super) fn object_prefix_covers(&self, object: &ObjectAccessFacts) -> bool {
        object.allocation_id.is_some_and(|id| {
            self.state.initialized_prefix_covers(
                id,
                object.shape.access(),
                crate::verifier::relation::range::access_range(
                    object.pointer,
                    object.shape.size_bytes(),
                ),
                self.relation_limits,
                &self.relations.queries,
            )
        })
    }

    pub(super) fn apply_object_write(
        &mut self,
        object: &ObjectAccessFacts,
        possible: &ByteSet,
        guaranteed: &ByteSet,
    ) -> Result<(), TransferError> {
        let Some(allocation_id) = object.allocation_id else {
            return Ok(());
        };
        let Some(allocation) = self.state.allocation_mut(allocation_id) else {
            return Ok(());
        };
        if !possible.is_precise() {
            if let Some(envelope) = object.envelope
                && envelope.end() <= allocation.size_bytes()
            {
                allocation.forget_initialization(envelope)?;
            }
        } else {
            for range in possible.ranges() {
                if let Some(range) = relative_access_envelope(object.pointer.offset_bytes(), *range)
                    && range.end() <= allocation.size_bytes()
                {
                    allocation.forget_initialization(range)?;
                }
            }
        }
        for range in guaranteed.ranges() {
            if let Some(range) = relative_definite_access(object.pointer.offset_bytes(), *range)
                && range.end() <= allocation.size_bytes()
            {
                allocation.mark_initialized(range)?;
                allocation.mark_valid(range)?;
            }
        }
        Ok(())
    }

    pub(super) fn apply_object_deinitialize(
        &mut self,
        object: &ObjectAccessFacts,
        mask: &ActiveObjectMask,
    ) -> Result<(), TransferError> {
        let Some(allocation_id) = object.allocation_id else {
            return Ok(());
        };
        let Some(allocation) = self.state.allocation_mut(allocation_id) else {
            return Ok(());
        };
        let empty_payloads = empty_resource_paths(allocation);
        if !mask.possible_value_bytes.is_precise() {
            if let Some(envelope) = object.envelope
                && envelope.end() <= allocation.size_bytes()
            {
                allocation.forget_initialization(envelope)?;
            }
        } else {
            for range in mask.possible_value_bytes.ranges() {
                if let Some(range) = relative_access_envelope(object.pointer.offset_bytes(), *range)
                    && range.end() <= allocation.size_bytes()
                {
                    allocation.forget_initialization(range)?;
                }
            }
        }
        // Forget the object-wide cache before installing definite retirement
        // facts. Doing this afterwards erased Moved payload paths established
        // by mark_uninitialized, making safe nested refill look Unknown.
        if let Some(envelope) = object.envelope
            && envelope.end() <= allocation.size_bytes()
        {
            allocation.forget_object_state(envelope)?;
        }
        for range in mask.guaranteed_value_bytes.ranges() {
            if let Some(range) = relative_definite_access(object.pointer.offset_bytes(), *range)
                && range.end() <= allocation.size_bytes()
            {
                allocation.mark_uninitialized(range)?;
            }
        }
        restore_empty_resource_paths(allocation, &empty_payloads)?;
        Ok(())
    }

    pub(super) fn apply_object_uninitialized(
        &mut self,
        object: &ObjectAccessFacts,
        relative_ranges: &ByteSet,
    ) -> Result<(), TransferError> {
        let Some(allocation_id) = object.allocation_id else {
            return Ok(());
        };
        let Some(allocation) = self.state.allocation_mut(allocation_id) else {
            return Ok(());
        };
        for range in relative_ranges.ranges() {
            if let Some(range) = relative_definite_access(object.pointer.offset_bytes(), *range)
                && range.end() <= allocation.size_bytes()
            {
                allocation.mark_uninitialized(range)?;
            }
        }
        Ok(())
    }

    pub(super) fn copy_active_variants(
        &mut self,
        source: &ObjectAccessFacts,
        destination: &ObjectAccessFacts,
        source_mask: &ActiveObjectMask,
    ) -> Result<(), TransferError> {
        let (Some(destination_id), Some(destination_base), Some(envelope)) = (
            destination.allocation_id,
            destination.pointer.offset_bytes().exact_value(),
            destination.envelope,
        ) else {
            return Ok(());
        };
        let Some(allocation) = self.state.allocation_mut(destination_id) else {
            return Ok(());
        };
        if envelope.end() <= allocation.size_bytes() {
            allocation.forget_object_state(envelope)?;
        }
        if source.allocation_id.is_none() || source.pointer.offset_bytes().exact_value().is_none() {
            return Ok(());
        }
        for (site, state, status) in &source_mask.sites {
            if *status != ObligationStatus::Proven || matches!(state, ActiveVariantState::Unknown) {
                continue;
            }
            let Some(offset) = destination_base.checked_add(site.offset_bytes) else {
                continue;
            };
            let _ = allocation
                .set_active_variant(ObjectStateKey::new(offset, site.access), state.clone())?;
        }
        Ok(())
    }

    pub(super) fn free(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, pointer_id)?;
        let permission = permission_fact(&self.state, permission_id)?;
        self.require(
            ResourceObligationKind::PointerProvenanceKnown {
                pointer: pointer_id,
            },
            known_provenance_status(pointer.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerAtAllocationBase {
                pointer: pointer_id,
            },
            base_pointer_status(pointer.offset_bytes()),
        );
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: permission_id,
            },
            permission_availability_status(permission.availability()),
        );
        self.require(
            ResourceObligationKind::PermissionCanFree {
                permission: permission_id,
            },
            free_capability_status(permission.free_capability()),
        );
        let full_access = match pointer.provenance() {
            AbstractProvenance::Known(allocation) => self
                .state
                .allocation(allocation)
                .and_then(|allocation| ByteRange::new(0, allocation.size_bytes()).ok()),
            AbstractProvenance::Unknown => None,
        };
        let (loan, loan_status) = permission_loan_access_status(
            &self.state,
            permission_id,
            permission,
            LoanAccess::whole(pointer, full_access, AccessPermission::Write),
            self.relation_limits,
            &self.relations,
        );
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan,
                permission: permission_id,
                access: full_access,
                required: AccessPermission::Write,
            },
            loan_status,
        );

        if let AbstractProvenance::Known(allocation_id) = pointer.provenance() {
            let allocation = self.state.allocation(allocation_id).cloned();
            self.require(
                ResourceObligationKind::AllocationTracked {
                    allocation: allocation_id,
                },
                if allocation.is_some() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
            self.require(
                ResourceObligationKind::PermissionMatchesAllocation {
                    permission: permission_id,
                    allocation: allocation_id,
                },
                provenance_match_status(permission.provenance(), allocation_id),
            );
            if let Some(allocation) = allocation {
                self.require(
                    ResourceObligationKind::AllocationLive {
                        allocation: allocation_id,
                    },
                    liveness_status(allocation.liveness()),
                );
                self.require(
                    ResourceObligationKind::AllocationOwned {
                        allocation: allocation_id,
                    },
                    ownership_status(allocation.ownership()),
                );
                self.require(
                    ResourceObligationKind::PermissionCoversAllocation {
                        permission: permission_id,
                        allocation: allocation_id,
                    },
                    full_permission_status(permission.range(), allocation.size_bytes()),
                );
                self.require(
                    ResourceObligationKind::AllocationResourcePayloadEmpty {
                        allocation: allocation_id,
                    },
                    allocation_resource_payload_empty_status(&allocation),
                );
                if let Some(allocation) = self.state.allocation_mut(allocation_id) {
                    allocation.mark_dead();
                }
            }
        }
        mark_permission_consumed(&mut self.state, permission_id)?;
        Ok(())
    }
}
