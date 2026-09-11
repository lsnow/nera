//! Shared typed object/slice access facts and permission obligations for call and memory effects.
//! Uses the same TransferBuilder, resource state and relation kernel as instruction transfer.
use super::{
    AbstractAllocation, AbstractAllocationId, AbstractPermission, AbstractPointer,
    AbstractProvenance, AccessPermission, ByteRange, InitializationClass, LivenessState,
    LoanAccess, ObligationStatus, ResourceObligationKind, SymbolicRangeBound, TransferBuilder,
    TransferError, VirMemoryAccess, VirObjectShape, VirValueId, abstract_range_from_offsets,
    access_envelope, add_pointer_intervals, known_provenance_status, liveness_status,
    memory_access_status, object_alignment_status, object_bounds_status,
    permission_availability_status, permission_fact, permission_loan_access_status,
    permission_writable_status, pointer_fact, provenance_match_status, scale_pointer_interval,
    symbolic_bound, word_expression, word_fact,
};

#[derive(Clone, Copy)]
pub(super) struct PermissionAccessContext {
    pub(super) allocation: Option<AbstractAllocationId>,
    pub(super) envelope: Option<ByteRange>,
    pub(super) pointer: AbstractPointer,
    pub(super) required_access: AccessPermission,
    pub(super) access_bytes: u64,
}

#[derive(Clone)]
pub(super) struct ObjectAccessFacts {
    pub(super) pointer: AbstractPointer,
    pub(super) allocation_id: Option<AbstractAllocationId>,
    pub(super) allocation: Option<AbstractAllocation>,
    pub(super) envelope: Option<ByteRange>,
    pub(super) shape: VirObjectShape,
}

impl TransferBuilder<'_> {
    pub(super) fn object_access_facts(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
        required_access: AccessPermission,
    ) -> Result<ObjectAccessFacts, TransferError> {
        let pointer = pointer_fact(&self.state, pointer_id)?;
        self.object_access_facts_for_pointer(
            pointer_id,
            permission_id,
            access,
            required_access,
            pointer,
        )
    }

    pub(super) fn object_access_facts_for_pointer(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        access: VirMemoryAccess,
        required_access: AccessPermission,
        pointer: AbstractPointer,
    ) -> Result<ObjectAccessFacts, TransferError> {
        let shape = self
            .memory
            .object_shape(access)
            .map_err(|_| TransferError::InvalidValidatedMemoryAccess(access))?;
        self.require_domain_access(pointer_id, pointer, shape.size_bytes());
        let permission = permission_fact(&self.state, permission_id)?;
        self.require(
            ResourceObligationKind::PointerProvenanceKnown {
                pointer: pointer_id,
            },
            known_provenance_status(pointer.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerMemoryAccessMatches {
                pointer: pointer_id,
                expected: access,
                found: pointer.memory_access(),
            },
            memory_access_status(pointer.memory_access(), access),
        );

        let envelope = access_envelope(pointer.offset_bytes(), shape.size_bytes());
        let allocation_id = match pointer.provenance() {
            AbstractProvenance::Known(id) => Some(id),
            AbstractProvenance::Unknown => None,
        };
        let allocation = allocation_id.and_then(|id| self.state.allocation(id).cloned());
        if let Some(id) = allocation_id {
            self.require(
                ResourceObligationKind::AllocationTracked { allocation: id },
                if allocation.is_some() {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
        }
        self.require(
            ResourceObligationKind::ObjectAllocationLive {
                pointer: pointer_id,
                allocation: allocation_id,
            },
            allocation
                .as_ref()
                .map_or(ObligationStatus::Unknown, |allocation| {
                    liveness_status(allocation.liveness())
                }),
        );
        self.require(
            ResourceObligationKind::ObjectWithinBounds {
                pointer: pointer_id,
                allocation: allocation_id,
                access: envelope,
                size_bytes: shape.size_bytes(),
            },
            allocation
                .as_ref()
                .map_or(ObligationStatus::Unknown, |allocation| {
                    object_bounds_status(
                        pointer.offset_bytes(),
                        shape.size_bytes(),
                        allocation.size_bytes(),
                    )
                }),
        );
        self.require(
            ResourceObligationKind::ObjectAligned {
                pointer: pointer_id,
                required_alignment: shape.alignment(),
            },
            allocation
                .as_ref()
                .map_or(ObligationStatus::Unknown, |allocation| {
                    object_alignment_status(pointer, allocation, shape.alignment())
                }),
        );
        self.permission_access_obligations(
            permission_id,
            permission,
            PermissionAccessContext {
                allocation: allocation_id,
                envelope,
                pointer,
                required_access,
                access_bytes: shape.size_bytes(),
            },
        );
        Ok(ObjectAccessFacts {
            pointer,
            allocation_id,
            allocation,
            envelope,
            shape,
        })
    }

    /// Rebuild the actual ABI selection from pointer AND length. The pointer's
    /// footprint alone cannot validate a mutated or unrelated length argument.
    pub(super) fn require_slice_argument(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        length_id: VirValueId,
        element: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let pointer = pointer_fact(&self.state, pointer_id)?;
        let permission = permission_fact(&self.state, permission_id)?;
        let length = word_fact(&self.state, length_id)?;
        let (stride, _) = self.access_shape(element)?;
        let (bytes, scale) = scale_pointer_interval(length, stride);
        let (end, add) = add_pointer_intervals(pointer.offset_bytes(), bytes);
        self.require(
            ResourceObligationKind::SliceRangeStrideNoOverflow {
                length_values: length,
                stride_bytes: stride,
            },
            scale,
        );
        self.require(
            ResourceObligationKind::AddressCalculationNoOverflow {
                base: pointer_id,
                delta: bytes,
            },
            add,
        );
        let start_expression = symbolic_bound(pointer.offset_bytes(), pointer.offset_expression())
            .map(SymbolicRangeBound::expression);
        let end_expression = start_expression
            .zip(
                word_expression(&self.state, length_id, length)
                    .and_then(|e| e.checked_scale(stride)),
            )
            .and_then(|(a, b)| a.checked_add(b));
        let actual = abstract_range_from_offsets(
            pointer.offset_bytes(),
            start_expression,
            end,
            end_expression,
        );
        let envelope = ByteRange::new(pointer.offset_bytes().lower(), end.upper()).ok();
        self.require(
            ResourceObligationKind::PermissionCoversAccess {
                permission: permission_id,
                access: envelope,
            },
            self.range_contains(permission.range(), actual),
        );
        if let AbstractProvenance::Known(id) = pointer.provenance() {
            let allocation = self.state.allocation(id);
            let prefix = self.state.initialized_prefix_covers(
                id,
                element,
                actual,
                self.relation_limits,
                &self.relations.queries,
            );
            let live_and_bounded = allocation.zip(envelope).is_some_and(|(a, r)| {
                a.liveness() == LivenessState::Live && r.end() <= a.size_bytes()
            });
            let initialized = live_and_bounded
                && (prefix
                    || allocation.zip(envelope).is_some_and(|(a, r)| {
                        a.initialization().classify(r) == InitializationClass::Initialized
                    }));
            let valid = live_and_bounded
                && (prefix
                    || allocation
                        .zip(envelope)
                        .is_some_and(|(a, r)| a.valid_value_bytes().contains(r)));
            self.require(
                ResourceObligationKind::MemoryInitialized {
                    allocation: id,
                    access: envelope,
                },
                if initialized {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
            self.require(
                ResourceObligationKind::ObjectRepresentationValid {
                    allocation: Some(id),
                    access: envelope,
                    object: element,
                },
                if valid {
                    ObligationStatus::Proven
                } else {
                    ObligationStatus::Unknown
                },
            );
        }
        Ok(())
    }

    pub(super) fn permission_access_obligations(
        &mut self,
        permission_id: VirValueId,
        permission: AbstractPermission,
        context: PermissionAccessContext,
    ) {
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: permission_id,
            },
            permission_availability_status(permission.availability()),
        );
        if let Some(allocation_id) = context.allocation {
            self.require(
                ResourceObligationKind::PermissionMatchesAllocation {
                    permission: permission_id,
                    allocation: allocation_id,
                },
                provenance_match_status(permission.provenance(), allocation_id),
            );
        }
        self.require(
            ResourceObligationKind::PermissionCoversAccess {
                permission: permission_id,
                access: context.envelope,
            },
            self.relations.queries.covers_access(
                &self.state,
                permission.range(),
                context.pointer,
                context.access_bytes,
                self.relation_limits,
            ),
        );
        if matches!(context.required_access, AccessPermission::Write) {
            self.require(
                ResourceObligationKind::PermissionWritable {
                    permission: permission_id,
                },
                permission_writable_status(permission.access()),
            );
        }
        let (loan, status) = permission_loan_access_status(
            &self.state,
            permission_id,
            permission,
            LoanAccess::bytes(
                context.pointer,
                context.access_bytes,
                context.required_access,
            ),
            self.relation_limits,
            &self.relations,
        );
        self.require(
            ResourceObligationKind::LoanCompatible {
                loan,
                permission: permission_id,
                access: context.envelope,
                required: context.required_access,
            },
            status,
        );
    }
}
