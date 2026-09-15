use super::*;

impl<'environment> TransferBuilder<'environment> {
    pub(super) fn index_address(
        &mut self,
        result: VirValue,
        base: VirValueId,
        index_id: VirValueId,
        access: AddressAccess,
        stride_bytes: u64,
        length: u64,
    ) -> Result<(), TransferError> {
        let index = word_fact(&self.state, index_id)?;
        let bounds = self.compare_words(
            RelationComparison::LessThan,
            word(index_id),
            RelationTerm::Constant(length),
        );
        self.require(
            ResourceObligationKind::IndexWithinBounds {
                index: index_id,
                values: index,
                length,
            },
            bounds,
        );
        let (delta, multiplication) = scale_pointer_interval(index, stride_bytes);
        self.require(
            ResourceObligationKind::IndexStrideNoOverflow {
                index: index_id,
                values: index,
                stride_bytes,
            },
            multiplication,
        );
        let expression = word_expression(&self.state, index_id, index)
            .and_then(|expression| expression.checked_scale(stride_bytes));
        let object_offsets = pointer_fact(&self.state, base)?
            .object_offsets()
            .offset_by_index(index, stride_bytes);
        self.typed_address(result, base, access, delta, expression)?;
        let source = pointer_fact(&self.state, base)?;
        self.set_pointer_paths(result.id, source.paths().element())?;
        let bytes = length
            .checked_mul(stride_bytes)
            .ok_or(TransferError::InvalidDerivedRange)?;
        self.set_pointer_domain(
            result.id,
            VirPointerDomain::Restricted(pointer_range(source, bytes)),
        )?;
        self.set_pointer_object_offsets(result.id, object_offsets, access.result)
    }

    pub(super) fn slice_index_address(
        &mut self,
        result: VirValue,
        base: VirValueId,
        index_id: VirValueId,
        length_id: VirValueId,
        element: VirMemoryAccess,
        stride_bytes: u64,
    ) -> Result<(), TransferError> {
        let index = word_fact(&self.state, index_id)?;
        let length = word_fact(&self.state, length_id)?;
        let bounds = self.compare_words(
            RelationComparison::LessThan,
            word(index_id),
            word(length_id),
        );
        self.require(
            ResourceObligationKind::SliceIndexWithinBounds {
                index: index_id,
                values: index,
                length: length_id,
                length_values: length,
            },
            bounds,
        );
        let (delta, multiplication) = scale_pointer_interval(index, stride_bytes);
        self.require(
            ResourceObligationKind::IndexStrideNoOverflow {
                index: index_id,
                values: index,
                stride_bytes,
            },
            multiplication,
        );
        let expression = word_expression(&self.state, index_id, index)
            .and_then(|expression| expression.checked_scale(stride_bytes));
        let object_offsets = pointer_fact(&self.state, base)?
            .object_offsets()
            .offset_by_index(index, stride_bytes);
        self.typed_address(
            result,
            base,
            AddressAccess {
                source: element,
                result: element,
            },
            delta,
            expression,
        )?;
        let source = pointer_fact(&self.state, base)?;
        self.set_pointer_domain(result.id, source.domain())?;
        self.set_pointer_paths(result.id, source.paths())?;
        self.set_pointer_object_offsets(result.id, object_offsets, element)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn slice_address(
        &mut self,
        pointer_result: VirValue,
        length_result: VirValue,
        base_id: VirValueId,
        start_id: VirValueId,
        end_id: VirValueId,
        source: VirMemoryAccess,
        slice: VirMemoryAccess,
        element: VirMemoryAccess,
        stride_bytes: u64,
        bounds: VirIndexBounds,
    ) -> Result<SliceAddressFacts, TransferError> {
        let start = word_fact(&self.state, start_id)?;
        let end = word_fact(&self.state, end_id)?;
        let length = match bounds {
            VirIndexBounds::Array { length } => U64Interval::exact(length),
            VirIndexBounds::Slice { length } => word_fact(&self.state, length)?,
        };
        self.require(
            ResourceObligationKind::SliceRangeOrdered {
                start: start_id,
                start_values: start,
                end: end_id,
                end_values: end,
            },
            self.compare_words(
                RelationComparison::LessOrEqual,
                word(start_id),
                word(end_id),
            ),
        );
        self.require(
            ResourceObligationKind::SliceRangeWithinBounds {
                end: end_id,
                end_values: end,
                length_values: length,
            },
            self.compare_words(
                RelationComparison::LessOrEqual,
                word(end_id),
                match bounds {
                    VirIndexBounds::Array { length } => RelationTerm::Constant(length),
                    VirIndexBounds::Slice { length } => word(length),
                },
            ),
        );

        let (start_delta, start_scale) = scale_pointer_interval(start, stride_bytes);
        let (end_delta, end_scale) = scale_pointer_interval(end, stride_bytes);
        let (source_delta, source_scale) = scale_pointer_interval(length, stride_bytes);
        self.require(
            ResourceObligationKind::SliceRangeStrideNoOverflow {
                length_values: length,
                stride_bytes,
            },
            source_scale,
        );
        self.require(
            ResourceObligationKind::IndexStrideNoOverflow {
                index: start_id,
                values: start,
                stride_bytes,
            },
            start_scale,
        );
        self.require(
            ResourceObligationKind::IndexStrideNoOverflow {
                index: end_id,
                values: end,
                stride_bytes,
            },
            end_scale,
        );

        let base = pointer_fact(&self.state, base_id)?;
        let expected_base_access = match bounds {
            VirIndexBounds::Array { .. } => source,
            VirIndexBounds::Slice { .. } => element,
        };
        self.require(
            ResourceObligationKind::PointerProvenanceKnown { pointer: base_id },
            known_provenance_status(base.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerMemoryAccessMatches {
                pointer: base_id,
                expected: expected_base_access,
                found: base.memory_access(),
            },
            memory_access_status(base.memory_access(), expected_base_access),
        );

        let (start_offset, start_add) = add_pointer_intervals(base.offset_bytes(), start_delta);
        let (end_offset, end_add) = add_pointer_intervals(base.offset_bytes(), end_delta);
        let (source_end, source_add) = add_pointer_intervals(base.offset_bytes(), source_delta);
        for (delta, status) in [
            (start_delta, start_add),
            (end_delta, end_add),
            (source_delta, source_add),
        ] {
            self.require(
                ResourceObligationKind::AddressCalculationNoOverflow {
                    base: base_id,
                    delta,
                },
                status,
            );
        }

        let base_expression = base.offset_expression().or_else(|| {
            base.offset_bytes()
                .exact_value()
                .map(AffineExpression::constant)
        });
        let scaled_expression = |id, interval| {
            word_expression(&self.state, id, interval)
                .and_then(|expression| expression.checked_scale(stride_bytes))
        };
        let start_expression = base_expression
            .zip(scaled_expression(start_id, start))
            .and_then(|(base, delta)| base.checked_add(delta));
        let end_expression = base_expression
            .zip(scaled_expression(end_id, end))
            .and_then(|(base, delta)| base.checked_add(delta));
        let source_end_expression = match bounds {
            VirIndexBounds::Array { length } => base_expression.and_then(|base| {
                length
                    .checked_mul(stride_bytes)
                    .and_then(|delta| base.checked_add_constant(delta))
            }),
            VirIndexBounds::Slice { length: length_id } => base_expression
                .zip(scaled_expression(length_id, length))
                .and_then(|(base, delta)| base.checked_add(delta)),
        };
        let selected_range =
            abstract_range_from_offsets(start_offset, start_expression, end_offset, end_expression);
        let source_range = abstract_range_from_offsets(
            base.offset_bytes(),
            base_expression,
            source_end,
            source_end_expression,
        );
        self.require_domain_range(base_id, base, source_range);

        let allocation_id = match base.provenance() {
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
        if let (Some(id), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AllocationLive { allocation: id },
                liveness_status(allocation.liveness()),
            );
            self.require(
                ResourceObligationKind::AccessWithinBounds {
                    allocation: id,
                    access: exact_abstract_range(source_range),
                    size_bytes: allocation.size_bytes(),
                },
                interval_le_status(source_end, U64Interval::exact(allocation.size_bytes())),
            );
        }

        let mutable = matches!(
            self.memory.kind(slice.ty),
            Some(VirMemoryTypeKind::Slice {
                mutability: VirMutability::Mutable,
                ..
            })
        );
        let start_alignment = start_expression.map_or_else(
            || offset_alignment(base.alignment(), start_delta),
            AffineExpression::guaranteed_alignment,
        );
        let derived = AbstractPointer::new(
            base.provenance(),
            start_offset,
            base.alignment().join(start_alignment),
        )
        .with_offset_expression(start_expression)
        .with_memory_access(Some(element))
        .with_domain(VirPointerDomain::Restricted(selected_range))
        .with_paths(match bounds {
            VirIndexBounds::Array { .. } => base.paths().element(),
            VirIndexBounds::Slice { .. } => base.paths().selected(),
        })
        .with_slice_footprint(
            ByteRange::new(start_offset.lower(), end_offset.upper())
                .ok()
                .map(|envelope| MemoryFootprint {
                    provenance: base.provenance(),
                    access: element,
                    stride_bytes,
                    range: selected_range,
                    envelope,
                }),
        )
        .with_object_offsets(base.object_offsets().offset_by_index(start, stride_bytes));
        let (_, element_alignment) = self.access_shape(element)?;
        if let (Some(_), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AddressObjectAligned {
                    pointer: pointer_result.id,
                    required_alignment: element_alignment,
                },
                object_alignment_status(derived, allocation, element_alignment),
            );
        }

        let exact_difference = word_expression(&self.state, start_id, start)
            .zip(word_expression(&self.state, end_id, end))
            .filter(|(a, b)| a.same_terms(*b))
            .and_then(|(a, b)| b.addend().checked_sub(a.addend()));
        let mut result_length =
            exact_difference.map_or_else(|| subtract_intervals(end, start), U64Interval::exact);
        if result_length.lower() == 0
            && result_length.upper() > 0
            && self
                .compare_words(RelationComparison::LessThan, word(start_id), word(end_id))
                .is_proven()
        {
            result_length = U64Interval::new(1, result_length.upper()).expect("nonempty range");
        }
        self.define(pointer_result, AbstractValue::Pointer(derived))?;
        self.define(length_result, AbstractValue::U64(result_length))?;
        if start.exact_value() == Some(0)
            && let Some(expression) = word_expression(&self.state, end_id, end)
        {
            self.state.set_word_expression(length_result.id, expression);
        }
        Ok(SliceAddressFacts {
            allocation_id,
            source_range,
            selected_range,
            mutable,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn slice_range(
        &mut self,
        pointer_result: VirValue,
        length_result: VirValue,
        permission_result: VirValue,
        base_id: VirValueId,
        permission_id: VirValueId,
        start_id: VirValueId,
        end_id: VirValueId,
        source: VirMemoryAccess,
        slice: VirMemoryAccess,
        element: VirMemoryAccess,
        stride_bytes: u64,
        bounds: VirIndexBounds,
    ) -> Result<(), TransferError> {
        let facts = self.slice_address(
            pointer_result,
            length_result,
            base_id,
            start_id,
            end_id,
            source,
            slice,
            element,
            stride_bytes,
            bounds,
        )?;
        let permission = permission_fact(&self.state, permission_id)?;
        self.require(
            ResourceObligationKind::PermissionAvailable {
                permission: permission_id,
            },
            permission_availability_status(permission.availability()),
        );
        if let Some(id) = facts.allocation_id {
            self.require(
                ResourceObligationKind::PermissionMatchesAllocation {
                    permission: permission_id,
                    allocation: id,
                },
                provenance_match_status(permission.provenance(), id),
            );
        }
        self.require(
            ResourceObligationKind::PermissionCoversAccess {
                permission: permission_id,
                access: exact_abstract_range(facts.source_range),
            },
            self.range_contains(permission.range(), facts.source_range),
        );
        if facts.mutable {
            self.require(
                ResourceObligationKind::PermissionWritable {
                    permission: permission_id,
                },
                permission_writable_status(permission.access()),
            );
        }
        let result_access = if facts.mutable {
            match permission.access() {
                AccessPermission::Write => AccessPermission::Write,
                AccessPermission::Read | AccessPermission::MaybeWrite => {
                    AccessPermission::MaybeWrite
                }
            }
        } else {
            AccessPermission::Read
        };
        mark_permission_consumed(&mut self.state, permission_id)?;
        self.move_loan_authority(permission.authority(), permission_id, permission_result.id);
        self.define(
            permission_result,
            AbstractValue::Permission(
                AbstractPermission::new(
                    permission.provenance(),
                    facts.selected_range,
                    result_access,
                    FreeCapability::No,
                )
                .with_authority(permission.authority()),
            ),
        )
    }

    pub(super) fn typed_address(
        &mut self,
        result: VirValue,
        base_id: VirValueId,
        access: AddressAccess,
        delta: U64Interval,
        delta_expression: Option<AffineExpression>,
    ) -> Result<(), TransferError> {
        let (source_bytes, source_alignment) = self.access_shape(access.source)?;
        let (result_bytes, result_alignment) = self.access_shape(access.result)?;
        let base = pointer_fact(&self.state, base_id)?;
        self.require_domain_access(base_id, base, source_bytes);
        self.require(
            ResourceObligationKind::PointerProvenanceKnown { pointer: base_id },
            known_provenance_status(base.provenance()),
        );
        self.require(
            ResourceObligationKind::PointerMemoryAccessMatches {
                pointer: base_id,
                expected: access.source,
                found: base.memory_access(),
            },
            memory_access_status(base.memory_access(), access.source),
        );

        let allocation_id = match base.provenance() {
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
        if let (Some(id), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AllocationLive { allocation: id },
                liveness_status(allocation.liveness()),
            );
            self.require(
                ResourceObligationKind::AddressObjectWithinBounds {
                    allocation: id,
                    offset: base.offset_bytes(),
                    object_bytes: source_bytes,
                    size_bytes: allocation.size_bytes(),
                },
                object_bounds_status(base.offset_bytes(), source_bytes, allocation.size_bytes()),
            );
            self.require(
                ResourceObligationKind::AddressObjectAligned {
                    pointer: base_id,
                    required_alignment: source_alignment,
                },
                object_alignment_status(base, allocation, source_alignment),
            );
        }

        let (offset, overflow) = add_pointer_intervals(base.offset_bytes(), delta);
        self.require(
            ResourceObligationKind::AddressCalculationNoOverflow {
                base: base_id,
                delta,
            },
            overflow,
        );
        let base_expression = base.offset_expression().or_else(|| {
            base.offset_bytes()
                .exact_value()
                .map(AffineExpression::constant)
        });
        let offset_expression = base_expression
            .zip(delta_expression)
            .and_then(|(base, delta)| base.checked_add(delta));
        let delta_alignment = delta_expression.map_or_else(
            || offset_alignment(base.alignment(), delta),
            AffineExpression::guaranteed_alignment,
        );
        let derived = AbstractPointer::new(
            base.provenance(),
            offset,
            base.alignment().join(delta_alignment),
        )
        .with_offset_expression(offset_expression)
        .with_memory_access(Some(access.result))
        .with_paths(crate::VirPointerPaths::default())
        .with_object_offsets(
            delta
                .exact_value()
                .map_or(AbstractObjectOffsets::Unknown, |delta| {
                    base.object_offsets().offset_by_exact(delta)
                }),
        );

        self.require_domain_range(base_id, base, pointer_range(derived, result_bytes));
        let derived = derived.with_domain(VirPointerDomain::Restricted(pointer_range(
            derived,
            result_bytes,
        )));

        if let (Some(id), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AddressObjectWithinBounds {
                    allocation: id,
                    offset,
                    object_bytes: result_bytes,
                    size_bytes: allocation.size_bytes(),
                },
                object_bounds_status(offset, result_bytes, allocation.size_bytes()),
            );
            self.require(
                ResourceObligationKind::AddressObjectAligned {
                    pointer: result.id,
                    required_alignment: result_alignment,
                },
                object_alignment_status(derived, allocation, result_alignment),
            );
        }
        self.define(result, AbstractValue::Pointer(derived))
    }

    pub(super) fn access_shape(
        &self,
        access: VirMemoryAccess,
    ) -> Result<(u64, u64), TransferError> {
        self.memory
            .layout(access.layout)
            .filter(|layout| layout.ty == access.ty)
            .map(|layout| (layout.size_bytes, layout.alignment))
            .ok_or(TransferError::InvalidValidatedMemoryAccess(access))
    }

    pub(super) fn pointer_offset(
        &mut self,
        result: VirValue,
        base_id: VirValueId,
        delta_id: VirValueId,
    ) -> Result<(), TransferError> {
        let base = pointer_fact(&self.state, base_id)?;
        let delta = word_fact(&self.state, delta_id)?;
        self.require_domain_access(base_id, base, 0);
        let delta_expression = word_expression(&self.state, delta_id, delta);
        self.require(
            ResourceObligationKind::PointerProvenanceKnown { pointer: base_id },
            known_provenance_status(base.provenance()),
        );

        let (offset, overflow_status) = add_pointer_intervals(base.offset_bytes(), delta);
        self.require(
            ResourceObligationKind::PointerOffsetNoOverflow {
                base: base_id,
                delta,
            },
            overflow_status,
        );

        if let AbstractProvenance::Known(allocation_id) = base.provenance() {
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
            if let Some(allocation) = allocation {
                self.require(
                    ResourceObligationKind::AllocationLive {
                        allocation: allocation_id,
                    },
                    liveness_status(allocation.liveness()),
                );
                let bounds = if offset.upper() <= allocation.size_bytes() {
                    ObligationStatus::Proven
                } else if offset.lower() > allocation.size_bytes() {
                    ObligationStatus::Refuted
                } else {
                    ObligationStatus::Unknown
                };
                self.require(
                    ResourceObligationKind::PointerOffsetWithinBounds {
                        allocation: allocation_id,
                        offset,
                        size_bytes: allocation.size_bytes(),
                    },
                    bounds,
                );
            }
        }

        let base_expression = base.offset_expression().or_else(|| {
            base.offset_bytes()
                .exact_value()
                .map(AffineExpression::constant)
        });
        let offset_expression = base_expression
            .zip(delta_expression)
            .and_then(|(base, delta)| base.checked_add(delta));
        let delta_alignment = delta_expression.map_or_else(
            || offset_alignment(base.alignment(), delta),
            AffineExpression::guaranteed_alignment,
        );
        let selection =
            abstract_range_from_offsets(offset, offset_expression, offset, offset_expression);
        self.require_domain_range(base_id, base, selection);
        self.define(
            result,
            AbstractValue::Pointer(
                AbstractPointer::new(
                    base.provenance(),
                    offset,
                    base.alignment().join(delta_alignment),
                )
                .with_offset_expression(offset_expression)
                .with_memory_access(base.memory_access())
                .with_paths(base.paths())
                .with_domain(base.domain())
                .with_slice_footprint(base.slice_footprint())
                .with_object_offsets(
                    delta
                        .exact_value()
                        .map_or(AbstractObjectOffsets::Unknown, |delta| {
                            base.object_offsets().offset_by_exact(delta)
                        }),
                ),
            ),
        )
    }

    pub(super) fn memory_access(
        &mut self,
        pointer_id: VirValueId,
        permission_id: VirValueId,
        required_access: AccessPermission,
        initialization: InitializationRequirement,
        effect: MemoryEffect,
        access: VirMemoryAccess,
    ) -> Result<(), TransferError> {
        let first_obligation = self.obligations.len();
        let (access_bytes, required_alignment) = self.access_shape(access)?;
        let pointer = pointer_fact(&self.state, pointer_id)?;
        let permission = permission_fact(&self.state, permission_id)?;
        self.require_domain_access(pointer_id, pointer, access_bytes);
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

        let envelope = access_envelope(pointer.offset_bytes(), access_bytes);
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

        if let (Some(id), Some(allocation)) = (allocation_id, allocation.as_ref()) {
            self.require(
                ResourceObligationKind::AllocationLive { allocation: id },
                liveness_status(allocation.liveness()),
            );
            self.require(
                ResourceObligationKind::AccessWithinBounds {
                    allocation: id,
                    access: envelope,
                    size_bytes: allocation.size_bytes(),
                },
                object_bounds_status(
                    pointer.offset_bytes(),
                    access_bytes,
                    allocation.size_bytes(),
                ),
            );
            self.require(
                ResourceObligationKind::AccessAligned {
                    pointer: pointer_id,
                    required_alignment,
                },
                object_alignment_status(pointer, allocation, required_alignment),
            );

            let mut status = envelope.map_or(ObligationStatus::Unknown, |range| {
                initialization_status(allocation.initialization().classify(range), initialization)
            });
            if matches!(initialization, InitializationRequirement::Initialized)
                && !status.is_proven()
                && self.state.initialized_prefix_covers(
                    id,
                    access,
                    crate::verifier::relation::range::access_range(pointer, access_bytes),
                    self.relation_limits,
                    &self.relations.queries,
                )
            {
                status = ObligationStatus::Proven;
            }
            match initialization {
                InitializationRequirement::None => {}
                InitializationRequirement::Initialized => self.require(
                    ResourceObligationKind::MemoryInitialized {
                        allocation: id,
                        access: envelope,
                    },
                    status,
                ),
                InitializationRequirement::Uninitialized => self.require(
                    ResourceObligationKind::MemoryUninitialized {
                        allocation: id,
                        access: envelope,
                    },
                    status,
                ),
            }
            self.active_variant_access_obligations(
                pointer_id,
                pointer,
                allocation,
                access,
                access_bytes,
            )?;
        }

        self.permission_access_obligations(
            permission_id,
            permission,
            PermissionAccessContext {
                allocation: allocation_id,
                envelope,
                pointer,
                required_access,
                access_bytes,
            },
        );

        if matches!(effect, MemoryEffect::WriteValue) {
            self.forget_uncertain_scalar_write(pointer, access_bytes);
            if let (Some(id), Some(possible)) = (allocation_id, envelope)
                && let Some(allocation) = self.state.allocation_mut(id)
                && possible.end() <= allocation.size_bytes()
            {
                allocation.forget_uninitialized(possible)?;
                if let Some(definite) = definite_write_range(pointer.offset_bytes(), access_bytes) {
                    allocation.mark_initialized(definite)?;
                    allocation.mark_valid(definite)?;
                }
            }
            if let Some(before) = allocation.as_ref()
                && self.obligations[first_obligation..]
                    .iter()
                    .all(|obligation| obligation.status().is_proven())
            {
                self.state.advance_initialization_prefixes(
                    before,
                    pointer,
                    access,
                    self.relation_limits,
                    &self.relations.queries,
                );
            }
        }
        Ok(())
    }
}
